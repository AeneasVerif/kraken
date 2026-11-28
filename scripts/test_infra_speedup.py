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
        self.assertEqual(len(sh.ALL_HUBS), 12)
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
                "LeanQbe/T/Examples/Kissat/Proof/Dimacs/Cert.lean",
                "LeanQbe/T/Examples/Kissat/BaseHub.lean",
            ],
        )
        self.assertIsNotNone(mods)
        assert mods is not None
        self.assertIn("LeanQbe.T.Examples.Kissat.Proof.Dimacs.Cert", mods)
        self.assertNotIn("LeanQbe.T.Examples.Kissat.BaseHub", mods)
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
                    "img/kissat_dual_arch_survival.svg",
                    "scripts/check.sh",
                    "scripts/headlines.d/core.txt",
                    "LeanQbe.lean",
                    "LeanQbeAmd64.lean",
                    "LeanQbe/T/Examples/Kissat/Proof/Dimacs/Cert.lean",
                    "LeanQbe/T/OptLemmas.lean",
                    "LeanQbe/T/Amd64/KissatPlainCert1.lean",
                    "LeanQbeTest/T/Smoke.lean",
                    "LeanQbeTest/T/KissatC0Test.lean",
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
            st.select_suites(["LeanQbe/T/Bootstrap0/Emit.lean"]),
            ["./test/bootstrap0/run_stage_c_native.sh"],
        )
        self.assertEqual(
            st.select_suites(["LeanQbe/T/Examples/Kissat/Src/Full.lean"]),
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

        self.assertEqual(
            classify(["scripts/preflight.sh", "scripts/select_tests.py", "img/kissat_dual_arch_survival.svg"]),
            "class0",
        )
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
            f"{pfx}Src.Full": f"{pfx}BaseHub",
            f"{pfx}Proof.Dimacs.Cert": f"{pfx}BaseHub",
            f"{pfx}Plain": f"{pfx}BaseHub",
            f"{pfx}Core": f"{pfx}BaseHub",
            f"{pfx}Build.Inl.Full": f"{pfx}BaseHub",
            f"{pfx}Build.Oracle.Float64": f"{pfx}BaseHub",
            f"{pfx}Build.Oracle.Amd64.Float64": "LeanQbeAmd64",
            f"{pfx}Build.Oracle.Arm64.Float64": "LeanQbeArm64",
            f"{pfx}Build.Amd64.Float64": "LeanQbeAmd64",
            f"{pfx}Build.Arm64.Float64": "LeanQbeArm64",
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
            ["LeanQbe", "LeanQbeAmd64", "LeanQbeArm64", "leanqbe", "leanqbe-arm64"],
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
        *,
        staged_files: dict[str, str] | None = None,
        untracked_files: dict[str, str] | None = None,
        remove_on_disk: tuple[str, ...] = (),
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
            if head_files:
                _git(root, "add", "-A")
                _git(root, "commit", "-m", "change")

            for rel, txt in (staged_files or {}).items():
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(txt, encoding="utf-8")
                _git(root, "add", rel)

            for rel, txt in (untracked_files or {}).items():
                p = root / rel
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(txt, encoding="utf-8")

            for rel in remove_on_disk:
                (root / rel).unlink()

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

    def test_preflight_450_decl_guard_all_kinds_and_diff_scoping(self) -> None:
        # 1. 500L `private meta def` outside Proof/ (SlabLayoutElab blind spot) MUST fail
        big_meta_def = (
            "module\nprivate meta def slabCommands (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 498)
            + "\n  return x\n"
        )
        res_meta = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/SlabLayoutElab.lean": big_meta_def},
        )
        self.assertNotEqual(res_meta.returncode, 0)
        self.assertIn("def `slabCommands` is 500 lines > 450", res_meta.stderr)

        # 2. Non-Proof `theorem`, `def`, and `Src/Full.lean` > 450L MUST fail; 450L exact passes
        big_nonproof_thm = (
            "module\npublic theorem big_logic_thm : True := by\n"
            + "\n".join(["  have h := True.intro"] * 449)
            + "\n  exact h\n"
        )
        res_thm = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/BigThm.lean": big_nonproof_thm},
        )
        self.assertNotEqual(res_thm.returncode, 0)
        self.assertIn("theorem `big_logic_thm` is 451 lines > 450", res_thm.stderr)

        big_src_full = (
            "module\ndef bigData : Nat :=\n"
            + "\n".join(["  1 +"] * 450)
            + "\n  0\n"
        )
        res_src_full = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Examples/Kissat/Src/Full.lean": big_src_full},
        )
        self.assertNotEqual(res_src_full.returncode, 0)
        self.assertIn("def `bigData` is 452 lines > 450", res_src_full.stderr)

        ok_meta_450 = (
            "module\nprivate meta def okCommands (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 448)
            + "\n  return x\n"
        )
        res_ok_450 = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/OkElab.lean": ok_meta_450},
        )
        self.assertEqual(res_ok_450.returncode, 0, res_ok_450.stdout + res_ok_450.stderr)

        # 3. Legacy `Kissat/Full*.lean` and `archive/` are excluded from new decl guard
        res_legacy = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Examples/Kissat/FullLegacyProof.lean": big_meta_def,
                "archive/ParkedOld.lean": big_meta_def,
            },
        )
        self.assertEqual(res_legacy.returncode, 0, res_legacy.stdout + res_legacy.stderr)

        # 4. Existing file: untouched pre-existing 480L decl & shrunk grandfathered decl pass;
        #    growing grandfathered decl or growing <=450L decl past 450L MUST fail!
        old_big = (
            "module\ndef tiny : Nat := 1\n\n"
            "def legacyBig (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 478)
            + "\n  return x\n"
        )
        old_big_edit_tiny = old_big.replace("def tiny : Nat := 1", "def tiny : Nat := 2")
        res_untouched = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/OldFile.lean": old_big},
            {"LeanQbe/T/OldFile.lean": old_big_edit_tiny},
        )
        self.assertEqual(
            res_untouched.returncode, 0, res_untouched.stdout + res_untouched.stderr
        )

        old_big_shrunk = (
            "module\ndef tiny : Nat := 1\n\n"
            "def legacyBig (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 468)
            + "\n  return x\n"
        )
        res_shrunk = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/OldFile.lean": old_big},
            {"LeanQbe/T/OldFile.lean": old_big_shrunk},
        )
        self.assertEqual(res_shrunk.returncode, 0, res_shrunk.stdout + res_shrunk.stderr)

        old_big_grown = (
            "module\ndef tiny : Nat := 1\n\n"
            "def legacyBig (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 483)
            + "\n  return x\n"
        )
        res_grown = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/OldFile.lean": old_big},
            {"LeanQbe/T/OldFile.lean": old_big_grown},
        )
        self.assertNotEqual(res_grown.returncode, 0)
        self.assertIn("grandfathered def `legacyBig` grew 480 -> 485", res_grown.stderr)

        old_small = (
            "module\ndef normalDef (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 398)
            + "\n  return x\n"
        )
        old_small_blown = (
            "module\ndef normalDef (n : Nat) : Nat := Id.run do\n"
            + "\n".join(["  let x := n"] * 458)
            + "\n  return x\n"
        )
        res_blown = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/GrowFile.lean": old_small},
            {"LeanQbe/T/GrowFile.lean": old_small_blown},
        )
        self.assertNotEqual(res_blown.returncode, 0)
        self.assertIn("def `normalDef` is 460 lines > 450", res_blown.stderr)

    def test_preflight_100_col_guard_including_comments_and_docstrings(self) -> None:
        # 1. New file: 105c doc-comment (`SlabLayout.lean:92` blind spot), `--` comment, `/-` comment
        doc_105 = "/-- " + ("a" * 98) + " -/"
        self.assertEqual(len(doc_105), 105)
        res_doc = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/SlabLayout.lean": f"module\n{doc_105}\ndef x : Nat := 1\n"},
        )
        self.assertNotEqual(res_doc.returncode, 0)
        self.assertIn("line width 105 > 100", res_doc.stderr)

        line_108 = "-- " + ("b" * 105)
        self.assertEqual(len(line_108), 108)
        res_line = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/WideComment.lean": f"module\n{line_108}\ndef x : Nat := 1\n"},
        )
        self.assertNotEqual(res_line.returncode, 0)
        self.assertIn("line width 108 > 100", res_line.stderr)

        block_104 = "/- " + ("c" * 98) + " -/"
        self.assertEqual(len(block_104), 104)
        res_block = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/WideBlock.lean": f"module\n{block_104}\ndef x : Nat := 1\n"},
        )
        self.assertNotEqual(res_block.returncode, 0)
        self.assertIn("line width 104 > 100", res_block.stderr)

        # 2. Exact 100c doc-comment passes cleanly
        doc_100 = "/-- " + ("d" * 93) + " -/"
        self.assertEqual(len(doc_100), 100)
        res_ok100 = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {"LeanQbe/T/Logic/Exact100.lean": f"module\n{doc_100}\ndef x : Nat := 1\n"},
        )
        self.assertEqual(res_ok100.returncode, 0, res_ok100.stdout + res_ok100.stderr)

        # 3. Existing file: untouched pre-existing 105c doc-comment passes; adding one fails
        old_wide = f"module\n{doc_105}\ndef x : Nat := 1\n"
        res_old_ok = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/Logic/Existing.lean": old_wide},
            {"LeanQbe/T/Logic/Existing.lean": f"module\n{doc_105}\ndef x : Nat := 2\n"},
        )
        self.assertEqual(res_old_ok.returncode, 0, res_old_ok.stdout + res_old_ok.stderr)

        res_old_bad = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/Logic/Existing.lean": old_wide},
            {
                "LeanQbe/T/Logic/Existing.lean": (
                    f"module\n{doc_105}\n{line_108}\ndef x : Nat := 2\n"
                )
            },
        )
        self.assertNotEqual(res_old_bad.returncode, 0)
        self.assertIn("Existing.lean:3: line width 108 > 100", res_old_bad.stderr)

    def test_preflight_rejects_untracked_and_missing_local_imports(self) -> None:
        # 1. Exact FrameCalc.lean trap: file exists on disk ONLY as untracked file -> MUST FAIL
        res_untracked = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Examples/Kissat/Proof/PropSearch/WpInnerBin.lean": (
                    "module\nimport LeanQbe.T.Logic.FrameCalc\ndef ok : Nat := 1\n"
                )
            },
            untracked_files={
                "LeanQbe/T/Logic/FrameCalc.lean": "module\ndef fc : Nat := 0\n"
            },
        )
        self.assertNotEqual(res_untracked.returncode, 0)
        self.assertIn("LeanQbe.T.Logic.FrameCalc", res_untracked.stderr)
        self.assertIn("is untracked", res_untracked.stderr)

        # 2. Untracked LeanQbeTest.* import -> MUST FAIL
        res_test_untracked = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbeTest/T/MyTest.lean": (
                    "module\npublic meta import LeanQbeTest.T.DraftHelper\n"
                )
            },
            untracked_files={
                "LeanQbeTest/T/DraftHelper.lean": "module\ndef h : Nat := 1\n"
            },
        )
        self.assertNotEqual(res_test_untracked.returncode, 0)
        self.assertIn("LeanQbeTest.T.DraftHelper", res_test_untracked.stderr)
        self.assertIn("is untracked", res_test_untracked.stderr)

        # 3. Missing local module (neither tracked nor on disk) -> MUST FAIL
        res_missing = self._run_preflight_in_temp_repo(
            {"README.md": "ok\n"},
            {
                "LeanQbe/T/Logic/UsesMissing.lean": (
                    "module\npublic import LeanQbe.T.Logic.DoesNotExist\n"
                )
            },
        )
        self.assertNotEqual(res_missing.returncode, 0)
        self.assertIn("LeanQbe.T.Logic.DoesNotExist", res_missing.stderr)
        self.assertIn("is missing / not git-tracked", res_missing.stderr)

        # 4. Tracked-in-index but deleted from disk -> MUST FAIL
        res_deleted = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/Logic/Gone.lean": "module\ndef g : Nat := 1\n"},
            {
                "LeanQbe/T/Logic/UsesGone.lean": (
                    "module\nimport LeanQbe.T.Logic.Gone\n"
                )
            },
            remove_on_disk=("LeanQbe/T/Logic/Gone.lean",),
        )
        self.assertNotEqual(res_deleted.returncode, 0)
        self.assertIn("missing from working tree", res_deleted.stderr)

        # 5. Tracked + staged-in-index + external Std/Lean + commented-out imports -> MUST PASS
        res_ok = self._run_preflight_in_temp_repo(
            {"LeanQbe/T/Logic/TrackedBase.lean": "module\ndef b : Nat := 1\n"},
            {
                "LeanQbe/T/Logic/ValidUser.lean": (
                    "module\n"
                    "-- import LeanQbe.T.Logic.FrameCalc\n"
                    "public import LeanQbe.T.Logic.TrackedBase\n"
                    "import LeanQbe.T.Logic.StagedHelper\n"
                    "public meta import Lean.Elab.Command\n"
                    "import Std.Data.HashMap\n"
                    "def u : Nat := 1\n"
                )
            },
            staged_files={
                "LeanQbe/T/Logic/StagedHelper.lean": "module\ndef s : Nat := 2\n"
            },
        )
        self.assertEqual(res_ok.returncode, 0, res_ok.stdout + res_ok.stderr)

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
        self.assertEqual(
            li.classify_scope_paths(["LeanQbe/T/Examples/Kissat/Build/Oracle/Amd64/Float64.lean"]),
            "x64",
        )
        self.assertEqual(
            li.classify_scope_paths(["LeanQbe/T/Examples/Kissat/Build/Oracle/Arm64/Float64.lean"]),
            "arm64",
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


class TestLakeExactRdepsAndM5(unittest.TestCase):
    """Covers exact Lean 4.37 / Lake 5.0 trace propagation and M5 `import all` checks."""

    def test_lake_trace_propagation_all_import_kinds(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            files = {
                "Seed.lean": "module\npublic def x : Nat := 1\n",
                "PrivHop.lean": "module\nimport Seed\n",
                "AfterPriv.lean": "module\npublic import PrivHop\n",
                "PubHop.lean": "module\npublic import Seed\n",
                "AfterPub.lean": "module\nimport PubHop\n",
                "MetaConsumer.lean": "module\nmeta import PrivHop\n",
                "AfterMeta.lean": "module\nimport MetaConsumer\n",
                "PubMetaPoison.lean": "module\npublic meta import PrivHop\n",
                "AfterPubMeta.lean": "module\nimport PubMetaPoison\n",
                "AllConsumer.lean": "module\nimport all Seed\n",
                "AfterAll.lean": "module\nimport all AllConsumer\n",
                "LegacyFile.lean": "import PrivHop\n",
            }
            for rel, body in files.items():
                (root / rel).write_text(body, encoding="utf-8")
            rel_paths = list(files)

            # 1. proof-body-only edit: ONLY Seed + import all chain + legacy non-module!
            r_proof = li.collect_lean_rdeps(
                root,
                ["Seed"],
                lean_rel_paths=rel_paths,
                barrels=frozenset(),
                trace_mode="lake",
                edit_kind="proof",
            )
            self.assertEqual(
                r_proof,
                ["AfterAll", "AllConsumer", "LegacyFile", "Seed"],
            )

            # 2. ir-only edit: walks private `import` via `metaTransTrace`, rebuilds
            # `meta import` and `public meta import` (plus normal consumers of `public meta`),
            # while plain `import` / `public import` do NOT rebuild!
            r_ir = li.collect_lean_rdeps(
                root,
                ["Seed"],
                lean_rel_paths=rel_paths,
                barrels=frozenset(),
                trace_mode="lake",
                edit_kind="ir",
            )
            self.assertEqual(
                r_ir,
                [
                    "AfterAll",
                    "AfterPubMeta",
                    "AllConsumer",
                    "LegacyFile",
                    "MetaConsumer",
                    "PubMetaPoison",
                    "Seed",
                ],
            )

            # 3. olean edit: private `import` is a 1-hop barrier (`PrivHop` rebuilds,
            # `AfterPriv` does NOT), `public import` propagates (`PubHop` + `AfterPub`),
            # `metaTransTrace` still walks `PrivHop` -> `MetaConsumer` & `PubMetaPoison`.
            r_olean = li.collect_lean_rdeps(
                root,
                ["Seed"],
                lean_rel_paths=rel_paths,
                barrels=frozenset(),
                trace_mode="lake",
                edit_kind="olean",
            )
            self.assertEqual(
                r_olean,
                [
                    "AfterAll",
                    "AfterPub",
                    "AfterPubMeta",
                    "AllConsumer",
                    "LegacyFile",
                    "MetaConsumer",
                    "PrivHop",
                    "PubHop",
                    "PubMetaPoison",
                    "Seed",
                ],
            )
            # Compare against legacy uniform graph mode (includes AfterPriv and AfterMeta)
            r_graph = li.collect_lean_rdeps(
                root,
                ["Seed"],
                lean_rel_paths=rel_paths,
                barrels=frozenset(),
                trace_mode="graph",
            )
            self.assertIn("AfterPriv", r_graph)
            self.assertIn("AfterMeta", r_graph)

    def test_classify_lean_diff_edit_kind_and_auto_rdeps(self) -> None:
        base_src = (
            "module\n"
            "public import LeanQbe.T.IL\n\n"
            "public section\n"
            "theorem foo (n : Nat) : n = n := by\n"
            "  rfl\n\n"
            "def helper : Nat := 1\n"
        )
        proof_edit = base_src.replace("  rfl", "  -- comment\n  exact Eq.refl n")
        self.assertEqual(li.classify_lean_diff_edit_kind(base_src, proof_edit), "proof")

        sig_edit = base_src.replace("n = n", "n + 0 = n")
        self.assertEqual(li.classify_lean_diff_edit_kind(base_src, sig_edit), "olean")

        def_edit = base_src.replace("def helper : Nat := 1", "def helper : Nat := 2")
        self.assertEqual(li.classify_lean_diff_edit_kind(base_src, def_edit), "olean")

        imp_edit = base_src.replace("public import LeanQbe.T.IL", "import LeanQbe.T.IL")
        self.assertEqual(li.classify_lean_diff_edit_kind(base_src, imp_edit), "olean")

        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp)
            (repo / "A.lean").write_text(
                "module\npublic section\ntheorem t : True := by\n  trivial\n",
                encoding="utf-8",
            )
            (repo / "B.lean").write_text("module\npublic import A\n", encoding="utf-8")
            _git(repo, "init")
            _git(repo, "config", "user.name", "Test")
            _git(repo, "config", "user.email", "test@example.com")
            _git(repo, "config", "commit.gpgsign", "false")
            _git(repo, "add", "-A")
            _git(repo, "commit", "-m", "base")
            base_sha = _git(repo, "rev-parse", "HEAD").stdout.strip()

            # Proof-body-only edit -> auto mode rebuilds ONLY A
            (repo / "A.lean").write_text(
                "module\npublic section\ntheorem t : True := by\n  exact True.intro\n",
                encoding="utf-8",
            )
            self.assertEqual(
                rs.compute_rdeps(repo, ["A.lean"], base=base_sha, edit_kind="auto"),
                ["A"],
            )
            # Signature edit -> auto mode rebuilds A and B
            (repo / "A.lean").write_text(
                "module\npublic section\ntheorem t : True ∧ True := by\n  exact ⟨trivial, trivial⟩\n",
                encoding="utf-8",
            )
            self.assertEqual(
                rs.compute_rdeps(repo, ["A.lean"], base=base_sha, edit_kind="auto"),
                ["A", "B"],
            )

    def test_real_repo_lake_exact_rdeps_cli_c0step_proof_vs_olean(self) -> None:
        proof_mods = rs.compute_rdeps(
            REPO_ROOT,
            ["LeanQbe/T/Logic/C0Step.lean"],
            trace_mode="lake",
            edit_kind="proof",
        )
        self.assertEqual(proof_mods, ["LeanQbe.T.Logic.C0Step"])

        res = subprocess.run(
            [
                sys.executable,
                "-B",
                str(SCRIPTS_DIR / "rdeps_scope.py"),
                "--root",
                str(REPO_ROOT),
                "--changed",
                "-",
                "--trace-mode",
                "lake",
                "--edit-kind",
                "proof",
            ],
            input="LeanQbe/T/Logic/C0Step.lean\n",
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        self.assertEqual(res.returncode, 0, res.stderr)
        self.assertEqual(res.stdout.strip().splitlines(), ["LeanQbe.T.Logic.C0Step"])

    def test_m5_hygiene_ban_all_import_all_and_allowlist(self) -> None:
        src = "module\nimport all Kraken.Mem\ndef x : Nat := 1\n"
        rep = li.audit_lean_source("LeanQbe/T/Example.lean", src)
        self.assertEqual(rep["import_all_lines"], [2])
        self.assertEqual(li.collect_hygiene_violations("LeanQbe/T/Example.lean", rep), [])
        errs = li.collect_hygiene_violations(
            "LeanQbe/T/Example.lean", rep, ban_all_import_all=True
        )
        self.assertEqual(len(errs), 1)
        self.assertIn("M5", errs[0])
        self.assertEqual(
            li.collect_hygiene_violations(
                "LeanQbe/T/Example.lean",
                rep,
                ban_all_import_all=True,
                import_all_allowlist={"LeanQbe/T/Example.lean"},
            ),
            [],
        )


if __name__ == "__main__":
    unittest.main()
