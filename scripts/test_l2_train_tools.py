#!/usr/bin/env python3
"""Unit & dry-run simulation tests for N9/N10/N11/N13 train tools."""

from __future__ import annotations

import fcntl
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))

import _common  # noqa: E402
import l2_audit as l2  # noqa: E402
import merge_train as mt  # noqa: E402
import prune_worktrees as pw  # noqa: E402


def _git(cwd: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(cwd), *args], text=True
    ).strip()


def _git_bare(bare: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "--git-dir", str(bare), *args], text=True
    ).strip()


def _commit_file(
    repo: Path, rel: str, content: str, msg: str
) -> str:
    p = repo / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(content, encoding="utf-8")
    _git(repo, "add", rel)
    _git(repo, "commit", "-m", msg)
    return _git(repo, "rev-parse", "HEAD")


class TestPruneWorktrees(unittest.TestCase):
    def test_safety_guards_and_apply(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            bare = root / "repo.git"
            _git(root, "init", "--bare", str(bare))

            seed = root / "seed"
            _git(root, "clone", str(bare), str(seed))
            _git(seed, "config", "user.name", "Test")
            _git(seed, "config", "user.email", "test@example.com")
            c0 = _commit_file(seed, "README.md", "hello\n", "init")
            _git(seed, "branch", "leanqbe/main")
            _git(seed, "push", "origin", "leanqbe/main")

            # Add an unmerged commit on another leanqbe/* ref.
            _git(seed, "checkout", "-b", "leanqbe/feat-a")
            c_anch = _commit_file(seed, "a.txt", "a\n", "feat-a")
            _git(seed, "push", "origin", "leanqbe/feat-a")

            # Add an unmerged commit with no leanqbe/* ref.
            _git(seed, "checkout", c0)
            _git(seed, "checkout", "-b", "scratch-unanchored")
            c_unanch = _commit_file(seed, "b.txt", "b\n", "unanchored")
            _git(seed, "push", "origin", "scratch-unanchored")

            # Secondary worktrees off bare repo.
            wt_anc_clean = root / "swarm-old-1111"
            wt_bee1 = root / "builds" / "bee-1" / "wt"
            wt_bee4 = root / "builds" / "bee-4" / "wt"
            wt_manual = root / "manual-clean-8888"
            wt_dirty = root / "swarm-dirty-2222"
            wt_pid = root / "swarm-livepid-3333"
            wt_swarm = root / "swarm-active-4444"
            wt_anch_other = root / "swarm-anchored-5555"
            wt_anch_own = root / "swarm-own-feat-6666"
            wt_unanch = root / "swarm-wip-7777"

            _git_bare(bare, "worktree", "add", "--detach", str(wt_anc_clean), c0)
            _git_bare(bare, "worktree", "add", "--detach", str(wt_bee1), c0)
            _git_bare(bare, "worktree", "add", "--detach", str(wt_bee4), c0)
            _git_bare(bare, "worktree", "add", "--detach", str(wt_manual), c0)
            _git_bare(bare, "worktree", "add", "--detach", str(wt_dirty), c0)
            (wt_dirty / "untracked.txt").write_text("wip\n", encoding="utf-8")
            _git_bare(bare, "worktree", "add", "--detach", str(wt_pid), c0)
            _git_bare(bare, "worktree", "add", "--detach", str(wt_swarm), c0)
            _git_bare(bare, "worktree", "add", "--detach", str(wt_anch_other), c_anch)
            _git_bare(bare, "worktree", "add", str(wt_anch_own), "leanqbe/feat-a")
            _git_bare(bare, "worktree", "add", "--detach", str(wt_unanch), c_unanch)

            # Simulate an active PID inside wt_pid and active swarm worker in wt_swarm.
            fake_procs = [(999999, str(wt_pid), "lean foo.lean")]
            active_workers = [("active", str(wt_swarm))]

            # 1. Default mode (all_anchored=False): only wt_anc_clean is prunable.
            decs = pw.classify_worktrees(
                bare,
                base_ref="refs/heads/leanqbe/main",
                all_anchored=False,
                include_vartmp=False,
                procs=fake_procs,
                active_workers=active_workers,
                cwd=seed,
            )
            by_path = {d.path: d for d in decs}
            self.assertEqual(by_path[str(wt_anc_clean)].action, "prune")
            self.assertEqual(by_path[str(wt_bee1)].action, "keep")
            self.assertEqual(by_path[str(wt_bee1)].reason, "protected_bee_wt")
            self.assertEqual(by_path[str(wt_bee4)].action, "keep")
            self.assertEqual(by_path[str(wt_bee4)].reason, "protected_bee_wt")
            self.assertEqual(by_path[str(wt_manual)].action, "keep")
            self.assertEqual(by_path[str(wt_manual)].reason, "non_swarm_excluded")
            self.assertEqual(by_path[str(wt_dirty)].action, "keep")
            self.assertEqual(by_path[str(wt_dirty)].reason, "dirty_worktree")
            self.assertEqual(by_path[str(wt_pid)].action, "keep")
            self.assertEqual(by_path[str(wt_pid)].reason, "active_pid")
            self.assertEqual(by_path[str(wt_swarm)].action, "keep")
            self.assertEqual(by_path[str(wt_swarm)].reason, "active_swarm_worker")
            self.assertEqual(by_path[str(wt_anch_other)].action, "keep")
            self.assertEqual(
                by_path[str(wt_anch_other)].reason, "anchored_only_needs_all_anchored"
            )
            self.assertEqual(by_path[str(wt_anch_own)].action, "keep")
            self.assertEqual(by_path[str(wt_unanch)].action, "keep")

            # Explicit --include-non-swarm prunes manual WT while keeping all bee-*/wt protected.
            decs_nonswarm = pw.classify_worktrees(
                bare,
                base_ref="refs/heads/leanqbe/main",
                all_anchored=False,
                include_vartmp=False,
                include_non_swarm=True,
                procs=fake_procs,
                active_workers=active_workers,
                cwd=seed,
            )
            by_ns = {d.path: d for d in decs_nonswarm}
            self.assertEqual(by_ns[str(wt_manual)].action, "prune")
            self.assertEqual(by_ns[str(wt_bee1)].action, "keep")
            self.assertEqual(by_ns[str(wt_bee1)].reason, "protected_bee_wt")
            self.assertEqual(by_ns[str(wt_bee4)].action, "keep")
            self.assertEqual(by_ns[str(wt_bee4)].reason, "protected_bee_wt")

            # 2. With all_anchored=True: wt_anch_other becomes prunable, own-branch stays kept.
            decs_anch = pw.classify_worktrees(
                bare,
                base_ref="refs/heads/leanqbe/main",
                all_anchored=True,
                include_vartmp=False,
                procs=fake_procs,
                active_workers=active_workers,
                cwd=seed,
            )
            by_anch = {d.path: d for d in decs_anch}
            self.assertEqual(by_anch[str(wt_anch_other)].action, "prune")
            self.assertEqual(by_anch[str(wt_anch_own)].action, "keep")

            # 3. `--apply` removes ONLY approved worktrees and keeps all protected ones.
            removed, errs = pw.apply_pruning(bare, decs_anch)
            self.assertEqual(errs, [])
            self.assertEqual(set(removed), {str(wt_anc_clean), str(wt_anch_other)})
            self.assertFalse(wt_anc_clean.exists())
            self.assertFalse(wt_anch_other.exists())
            self.assertTrue(wt_bee1.exists())
            self.assertTrue(wt_bee4.exists())
            self.assertTrue(wt_manual.exists())
            self.assertTrue(wt_dirty.exists())
            self.assertTrue(wt_pid.exists())
            self.assertTrue(wt_swarm.exists())
            self.assertTrue(wt_anch_own.exists())
            self.assertTrue(wt_unanch.exists())

    def test_vartmp_and_dead_cache_guards(self) -> None:
        self.assertTrue(pw.is_vartmp_path(Path("/var/tmp/l2-review-foo")))
        self.assertFalse(pw.is_vartmp_path(Path("/tmp/other")))

        with tempfile.TemporaryDirectory() as td:
            home = Path(td)
            active = home / ".elan" / "cache"
            dead = home / ".cache" / "lake"
            (dead / "artifacts").mkdir(parents=True)
            (dead / "artifacts" / "blob.olean").write_bytes(b"x" * 4096)
            (active).mkdir(parents=True)

            old_env = os.environ.get("LAKE_CACHE_DIR")
            os.environ["LAKE_CACHE_DIR"] = str(active)
            try:
                # Dry-run with --prune-dead-cache must NOT delete dead cache.
                _, reps = pw.find_dead_lake_caches(
                    REPO_ROOT, home=home, apply=False, prune_dead_cache=True
                )
                self.assertEqual(len(reps), 1)
                self.assertEqual(reps[0].action, "prune")
                self.assertTrue(dead.exists())

                # Apply WITHOUT --prune-dead-cache must NOT delete dead cache.
                _, reps2 = pw.find_dead_lake_caches(
                    REPO_ROOT, home=home, apply=True, prune_dead_cache=False
                )
                self.assertEqual(reps2[0].action, "report")
                self.assertTrue(dead.exists())

                # Apply WITH --prune-dead-cache removes dead cache.
                _, reps3 = pw.find_dead_lake_caches(
                    REPO_ROOT, home=home, apply=True, prune_dead_cache=True
                )
                self.assertEqual(reps3[0].action, "removed")
                self.assertFalse(dead.exists())
            finally:
                if old_env is None:
                    os.environ.pop("LAKE_CACHE_DIR", None)
                else:
                    os.environ["LAKE_CACHE_DIR"] = old_env

    def test_live_dry_run_zero_mutations(self) -> None:
        res = subprocess.run(
            [
                sys.executable,
                "-B",
                str(SCRIPTS_DIR / "prune_worktrees.py"),
                "--root",
                str(REPO_ROOT),
                "--dry-run",
                "--json",
            ],
            capture_output=True,
            text=True,
            timeout=60,
            check=True,
        )
        data = json.loads(res.stdout)
        self.assertEqual(data["mode"], "dry-run")
        self.assertGreater(data["total_worktrees"], 0)
        self.assertGreaterEqual(data["reclaimable_gib"], 0.0)
        self.assertEqual(data["removed_worktrees"], [])
        for d in data["prunable_worktrees"]:
            self.assertFalse(pw.is_bee_wt(Path(d["path"])))
            self.assertFalse(d["path"].startswith("/var/tmp/"))
            self.assertTrue(Path(d["path"]).name.startswith("swarm-"))


class TestL2Audit(unittest.TestCase):
    def test_static_lean_hygiene(self) -> None:
        good = (
            "module\npublic import LeanQbe.T.IL\n"
            "@[expose] def x : Nat := 1\ntheorem ok : 1 = 1 := rfl\n"
        )
        rep = l2.audit_lean_text("Good.lean", good)
        self.assertFalse(rep["over_loc"])
        self.assertEqual(rep["long_lines"], [])
        self.assertEqual(rep["expose_on_thm"], [])
        self.assertEqual(rep["banned_hits"], [])
        self.assertEqual(rep["bad_import_all"], [])

        bad = "\n".join(
            [
                "module",
                "public import all LeanQbe.T.IL",
                "@[expose] theorem bad1 : True := trivial",
                "@[expose]",
                "private lemma bad2 : True := trivial",
                f"def wide : String := {'x' * 105}",
                "theorem s : False := sorry",
            ]
        )
        rep_bad = l2.audit_lean_text("Bad.lean", bad)
        self.assertEqual(rep_bad["expose_on_thm"], [3, 5])
        self.assertEqual(rep_bad["bad_import_all"], [2])
        self.assertEqual(len(rep_bad["long_lines"]), 1)
        self.assertEqual(len(rep_bad["banned_hits"]), 1)

        too_long = "\n".join(["-- line"] * 2500)
        self.assertTrue(l2.audit_lean_text("Huge.lean", too_long)["over_loc"])

        # P0-5 Proof/ rules and axiom / multiline @[extern] checks
        proof_bad = "\n".join(
            [
                "module",
                "import all Kraken.Mem",
                "@[expose] public section",
                "theorem bad_in_expose : True := trivial",
                "axiom ax_bad : False",
            ]
        )
        rep_p = l2.audit_lean_text(
            "LeanQbe/T/Examples/Kissat/Proof/BadProof.lean", proof_bad
        )
        self.assertEqual(rep_p["proof_import_all"], [2])
        self.assertEqual(
            rep_p["proof_expose_section"], [{"section_line": 3, "theorem_line": 4}]
        )
        self.assertEqual(len(rep_p["banned_hits"]), 1)

        # Data defs in Proof/Spec or closed @[expose] public section must not false-positive
        proof_spec_ok = "\n".join(
            [
                "module",
                "@[expose] public section",
                "structure SpecState where",
                "  x : Nat",
                "end",
                "public section",
                "@[expose] def helper : Nat := 1",
                "theorem ok_thm : helper = 1 := rfl",
            ]
        )
        rep_spec = l2.audit_lean_text(
            "LeanQbe/T/Examples/Kissat/Proof/Spec/OkSpec.lean", proof_spec_ok
        )
        self.assertEqual(rep_spec["proof_import_all"], [])
        self.assertEqual(rep_spec["proof_expose_section"], [])
        self.assertEqual(rep_spec["expose_on_thm"], [])

    def test_wrap_build_cmd_swap_and_slice_flags(self) -> None:
        cmd = l2.wrap_build_cmd(["lake", "build"], memory_max="12G", use_systemd=True)
        self.assertEqual(cmd[0], "systemd-run")
        self.assertIn("--slice=leanqbe-builds.slice", cmd)
        self.assertIn("MemorySwapMax=0", cmd)
        self.assertIn("MemoryMax=12G", cmd)
        self.assertIn("OOMPolicy=kill", cmd)

    def test_common_run_cgroup_and_build_cmd(self) -> None:
        scoped = _common.build_cgroup_cmd(
            ["lake", "build"],
            memory_max="10G",
            timeout_sec=60,
            env_vars={"LAKE_ARTIFACT_CACHE": "true"},
            unit_name="u-test",
            use_systemd=True,
        )
        self.assertEqual(
            scoped,
            [
                "systemd-run",
                "--user",
                "--scope",
                "--quiet",
                "--unit=u-test",
                "--slice=leanqbe-builds.slice",
                "-p",
                "MemoryMax=10G",
                "-p",
                "MemorySwapMax=0",
                "-p",
                "OOMPolicy=kill",
                "timeout",
                "--foreground",
                "60",
                "env",
                "LAKE_ARTIFACT_CACHE=true",
                "lake",
                "build",
            ],
        )
        direct = _common.build_cgroup_cmd(
            ["lake", "build"], timeout_sec=0, use_systemd=False
        )
        self.assertEqual(direct, ["lake", "build"])

        seen: list[tuple[list[str], dict[str, object]]] = []

        def fake_runner(
            cmd: list[str], **kwargs: object
        ) -> subprocess.CompletedProcess[str]:
            seen.append((cmd, kwargs))
            return subprocess.CompletedProcess(
                args=cmd, returncode=0, stdout="ok\n", stderr=""
            )

        proc = _common.run_cgroup(
            ["lake", "build"],
            memory_max="8G",
            timeout_sec=30,
            use_systemd=False,
            runner=fake_runner,
            check=False,
        )
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(len(seen), 1)
        self.assertEqual(
            seen[0][0], ["timeout", "--foreground", "30", "lake", "build"]
        )

    def test_audit_static_hygiene_grandfathered_loc(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _git(repo, "init", "-b", "leanqbe/main")
            _git(repo, "config", "user.name", "Test")
            _git(repo, "config", "user.email", "test@example.com")
            c_base = _commit_file(
                repo, "Big.lean", "\n".join(["-- line"] * 2600) + "\n", "base"
            )
            c_shrink = _commit_file(
                repo, "Big.lean", "\n".join(["-- line"] * 2590) + "\n", "shrink"
            )
            res_ok = l2.audit_static_hygiene(
                repo, c_shrink, ["Big.lean"], set(), base_sha=c_base
            )
            self.assertEqual(res_ok["status"], "pass", res_ok)

            c_grow = _commit_file(
                repo, "Big.lean", "\n".join(["-- line"] * 2605) + "\n", "grow"
            )
            res_fail = l2.audit_static_hygiene(
                repo, c_grow, ["Big.lean"], set(), base_sha=c_base
            )
            self.assertEqual(res_fail["status"], "fail", res_fail)
            self.assertIn("grew 2600 -> 2605", res_fail["violations"][0])

    def test_c0_memo_cache_roundtrip(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            cache = Path(td) / "c0_memo.json"
            key = "fidelity:abc123"
            l2.save_c0_memo(cache, {key: {"verified": True, "c0_sha256": "abc123"}})
            loaded = l2.load_c0_memo(cache)
            self.assertTrue(loaded[key]["verified"])

    def test_dry_run_eacdd8ba_vs_4fa7421b(self) -> None:
        report = l2.run_audit(
            REPO_ROOT,
            "4fa7421b",
            "eacdd8ba",
            main_ref="4fa7421b",
            dry_run=True,
        )
        self.assertTrue(report["ok"], report)
        st = report["steps"]
        self.assertEqual(st["merge_tree"]["status"], "pass")
        self.assertEqual(st["sync_hubs"]["status"], "pass")
        self.assertEqual(st["check_firewall"]["status"], "pass")
        self.assertFalse(st["rdeps_canary"]["canary_triggered"])
        self.assertFalse(st["rdeps_canary"]["rdeps_capped_pass"])

    def test_dry_run_f4e4c39f_canary_frontier_simulation(self) -> None:
        base_f4 = _git(REPO_ROOT, "merge-base", "4fa7421b", "f4e4c39f")
        report = l2.run_audit(
            REPO_ROOT,
            base_f4,
            "f4e4c39f",
            main_ref="4fa7421b",
            dry_run=True,
        )
        # f4e4c39f conflicts on LeanQbe-README.md against 4fa7421b and touches IL/Main/Target.
        st = report["steps"]
        self.assertEqual(st["merge_tree"]["status"], "fail")
        self.assertTrue(st["rdeps_canary"]["canary_triggered"])
        self.assertGreater(st["rdeps_canary"]["exact_rdeps_count"], 50)
        self.assertIn(
            "LeanQbe.T.CoreHub", st["rdeps_canary"]["canary_present"]
        )
        self.assertIn(
            "LeanQbe.T.Wasm.BulkSafety", st["rdeps_canary"]["canary_present"]
        )

        # `--allow` rejects mismatched paths deterministically.
        blocked = l2.run_audit(
            REPO_ROOT,
            base_f4,
            "f4e4c39f",
            main_ref="4fa7421b",
            allow_regex=r"^docs/",
            dry_run=True,
        )
        self.assertEqual(blocked["steps"]["diff_stats"]["status"], "fail")
        self.assertIn(
            "LeanQbe/T/IL.lean",
            blocked["steps"]["diff_stats"]["disallowed_files"],
        )

    def test_pooled_worktree_reset_before_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo = root / "repo"
            repo.mkdir()
            _git(repo, "init", "-b", "leanqbe/main")
            _git(repo, "config", "user.name", "Test")
            _git(repo, "config", "user.email", "test@example.com")
            c1 = _commit_file(repo, "f.txt", "v1\n", "v1")
            c2 = _commit_file(repo, "f.txt", "v2\n", "v2")

            pool = root / "pool"
            with l2.target_worktree_ctx(
                repo, c1, worktree_pool=pool, dry_run=False
            ) as wt:
                self.assertEqual(_git(wt, "rev-parse", "HEAD"), c1)
                (wt / "f.txt").write_text("dirty\n", encoding="utf-8")
                (wt / "untracked.txt").write_text("trash\n", encoding="utf-8")
                (wt / ".lake").mkdir()
                (wt / ".lake" / "keep.txt").write_text("ok\n", encoding="utf-8")

            with l2.target_worktree_ctx(
                repo, c2, worktree_pool=pool, dry_run=False
            ) as wt:
                self.assertEqual(_git(wt, "rev-parse", "HEAD"), c2)
                self.assertEqual(
                    (wt / "f.txt").read_text(encoding="utf-8"), "v2\n"
                )
                self.assertFalse((wt / "untracked.txt").exists())
                self.assertTrue((wt / ".lake" / "keep.txt").exists())
            _git(repo, "worktree", "remove", "--force", str(pool))

    def test_axiom_audit_chunks_le_12(self) -> None:
        mods = [
            f"LeanQbe.T.{p.stem}"
            for p in sorted((REPO_ROOT / "LeanQbe" / "T").glob("*.lean"))
        ][:26]
        self.assertGreater(len(mods), 12)
        plan = l2.run_axiom_audit(REPO_ROOT, mods, dry_run=True)
        self.assertEqual(plan["status"], "planned")
        groups = plan["groups"]
        self.assertGreater(len(groups), 1)
        seen: list[str] = []
        for g in groups:
            self.assertLessEqual(len(g["modules"]), 12)
            seen.extend(g["modules"])
        self.assertEqual(sorted(seen), sorted(mods))
        active_groups = [g for g in groups if g["headline_consts"] > 0]
        self.assertGreaterEqual(len(active_groups), 1)

        # Compiled `audit_axioms` backend: single combined manifest invocation.
        manifests: list[str] = []

        def fake_bin_run(
            cmd: list[str], **kwargs: object
        ) -> subprocess.CompletedProcess[str]:
            manifests.append(Path(cmd[-1]).read_text(encoding="utf-8"))
            return subprocess.CompletedProcess(
                args=cmd,
                returncode=0,
                stdout="audit_axioms: TOTAL ok\n",
                stderr="",
            )

        with (
            mock.patch.object(
                l2, "resolve_audit_axioms_bin", return_value=Path("/tmp/fake_audit_axioms")
            ),
            mock.patch.object(l2, "systemd_scope_available", return_value=False),
            mock.patch.object(l2.subprocess, "run", side_effect=fake_bin_run) as m_bin,
        ):
            live = l2.run_axiom_audit(REPO_ROOT, mods, dry_run=False)
        self.assertEqual(live["status"], "pass")
        self.assertEqual(live["backend"], "audit_axioms")
        self.assertEqual(m_bin.call_count, 1)
        self.assertEqual(len(live["chunk_runs"]), len(active_groups))
        self.assertIn(f"GROUP {active_groups[0]['group']}", manifests[0])

        # Safe fallback when `audit_axioms` binary is unavailable.
        fake_fb = subprocess.CompletedProcess(
            args=[], returncode=0, stdout="audit_axioms [generic_1]: ok\n", stderr=""
        )
        with (
            mock.patch.object(l2, "resolve_audit_axioms_bin", return_value=None),
            mock.patch.object(l2, "systemd_scope_available", return_value=False),
            mock.patch.object(l2.subprocess, "run", return_value=fake_fb) as m_fb,
        ):
            fb = l2.run_axiom_audit(REPO_ROOT, mods, dry_run=False)
        self.assertEqual(fb["status"], "pass")
        self.assertEqual(fb["backend"], "lean_run_fallback")
        self.assertEqual(m_fb.call_count, len(active_groups))
        self.assertEqual(len(fb["chunk_runs"]), len(active_groups))
        for call in m_fb.call_args_list:
            self.assertIn("AuditAxioms.lean", " ".join(call.args[0]))

    def test_live_kernel_axiom_audit_cached_module(self) -> None:
        if os.environ.get("CHECK_NO_LAKE_TESTS") == "1":
            self.skipTest("CHECK_NO_LAKE_TESTS=1")
        build_res = l2.execute_lake_build(
            REPO_ROOT, ["LeanQbeTest.T.Amd64FrameTest"]
        )
        self.assertEqual(build_res["status"], "pass", build_res)
        res = l2.run_axiom_audit(
            REPO_ROOT, ["LeanQbeTest.T.Amd64FrameTest"], dry_run=False
        )
        self.assertEqual(res["status"], "pass", res)
        self.assertIn("x64", str(res["stdout"]))
        self.assertTrue(
            "audit_axioms" in str(res["stdout"]) or "AXIOM_GROUP" in str(res["stdout"]),
            str(res["stdout"]),
        )


class TestMergeTrain(unittest.TestCase):
    def test_bisect_ologk_single_and_multi_failures(self) -> None:
        items = list(range(8))
        # All pass -> 1 test evaluation.
        trace0: list[dict[str, object]] = []
        good0, bad0 = mt.bisect_candidates(
            items, lambda s: (True, {}), trace=trace0
        )
        self.assertEqual(good0, items)
        self.assertEqual(bad0, [])
        self.assertEqual(len(trace0), 1)

        # Single bad item at each position -> O(log k) steps (<= 9 for k=8).
        for culprit in items:
            trace: list[dict[str, object]] = []
            good, bad = mt.bisect_candidates(
                items,
                lambda s, c=culprit: (c not in s, {"bad": c}),
                trace=trace,
            )
            self.assertEqual(good, [x for x in items if x != culprit])
            self.assertEqual([x for x, _ in bad], [culprit])
            self.assertLessEqual(len(trace), 9)

        # Pairwise clash: 1 and 5 pass alone, fail together -> 1 kept, 5 ejected.
        trace_p: list[dict[str, object]] = []
        good_p, bad_p = mt.bisect_candidates(
            items,
            lambda s: (not (1 in s and 5 in s), {"reason": "pair_clash"}),
            trace=trace_p,
        )
        self.assertEqual(good_p, [0, 1, 2, 3, 4, 6, 7])
        self.assertEqual([x for x, _ in bad_p], [5])

    def test_dry_run_merge_train_conflicts_and_n8(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td) / "repo"
            repo.mkdir()
            _git(repo, "init", "-b", "leanqbe/main")
            _git(repo, "config", "user.name", "Test")
            _git(repo, "config", "user.email", "test@example.com")
            _commit_file(repo, "shared.txt", "line1\n", "base")

            # pr1: clean additive file
            _git(repo, "checkout", "-b", "pr1", "leanqbe/main")
            _commit_file(repo, "p1.txt", "one\n", "STANDALONE_GREEN p1")

            # pr2: touches shared.txt
            _git(repo, "checkout", "-b", "pr2", "leanqbe/main")
            _commit_file(repo, "shared.txt", "from pr2\n", "pr2")

            # pr3: conflicts with pr2 on shared.txt
            _git(repo, "checkout", "-b", "pr3", "leanqbe/main")
            _commit_file(repo, "shared.txt", "from pr3\n", "pr3")

            # pr4: marked TRAIN_SHARD (blocked by N8)
            _git(repo, "checkout", "-b", "pr4", "leanqbe/main")
            _commit_file(repo, "p4.txt", "four\n", "feat: TRAIN_SHARD partial")

            _git(repo, "checkout", "leanqbe/main")
            rep = mt.run_merge_train(
                repo,
                ["pr1", "pr2", "pr3", "pr4"],
                base_ref="leanqbe/main",
                dry_run=True,
            )
            self.assertTrue(rep["ok"])
            self.assertEqual(
                [c["branch"] for c in rep["accepted"]], ["pr1", "pr2"]
            )
            ejected = {e["branch"]: e["reason"] for e in rep["ejected"]}
            self.assertEqual(ejected["pr3"], "pairwise_merge_conflict")
            self.assertEqual(ejected["pr4"], "n8_train_shard")

    def test_staging_sync_hubs_and_execute_fast_land_stub(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo = root / "repo"
            repo.mkdir()
            _git(repo, "init", "-b", "leanqbe/main")
            _git(repo, "config", "user.name", "Test")
            _git(repo, "config", "user.email", "test@example.com")

            scripts = repo / "scripts"
            scripts.mkdir()
            (scripts / "sync_hubs.py").write_text(
                "import pathlib, sys\n"
                "r = pathlib.Path(sys.argv[sys.argv.index('--root') + 1])\n"
                "if '--write' in sys.argv:\n"
                "  (r / 'hub.txt').write_text('synced\\n')\n",
                encoding="utf-8",
            )
            (scripts / "check_firewall.py").write_text(
                "print('{\"leak_groups\": 0}')\n",
                encoding="utf-8",
            )
            marker = root / "fast_land_called.txt"
            (scripts / "fast_land.sh").write_text(
                "#!/usr/bin/env bash\n"
                f"echo \"$*\" > '{marker}'\n",
                encoding="utf-8",
            )
            os.chmod(scripts / "fast_land.sh", 0o755)
            _git(repo, "add", "scripts")
            _git(repo, "commit", "-m", "base scripts")

            _git(repo, "checkout", "-b", "pr-good", "leanqbe/main")
            _commit_file(repo, "notes.md", "ok\n", "docs: add notes")

            _git(repo, "checkout", "leanqbe/main")
            wt = root / "staging-wt"
            rep = mt.run_merge_train(
                repo,
                ["pr-good"],
                base_ref="leanqbe/main",
                worktree=wt,
                dry_run=False,
                execute=True,
                fast_land_skip_tests=True,
            )
            self.assertTrue(rep["ok"], rep)
            self.assertEqual(rep["fast_land"]["status"], "pass")
            self.assertTrue(marker.is_file())
            called_args = marker.read_text(encoding="utf-8").strip()
            self.assertIn("--fast", called_args)
            self.assertIn(str(rep["merged_sha"]), called_args)
            _git(repo, "worktree", "remove", "--force", str(wt))

    def _init_lane_test_repo(self, root: Path) -> tuple[Path, str]:
        repo = root / "repo"
        repo.mkdir()
        _git(repo, "init", "-b", "leanqbe/main")
        _git(repo, "config", "user.name", "Test")
        _git(repo, "config", "user.email", "test@example.com")

        scripts = repo / "scripts"
        scripts.mkdir()
        (scripts / "sync_hubs.py").write_text(
            "import pathlib, sys\n"
            "r = pathlib.Path(sys.argv[sys.argv.index('--root') + 1])\n"
            "if '--write' in sys.argv:\n"
            "  pass\n",
            encoding="utf-8",
        )
        (scripts / "check_firewall.py").write_text(
            "print('{\"leak_groups\": 0}')\n",
            encoding="utf-8",
        )
        (repo / "LeanQbe.lean").write_text("module\n", encoding="utf-8")
        (repo / "README.md").write_text("leanqbe\n", encoding="utf-8")
        (repo / "lakefile.toml").write_text("name = \"leanqbe\"\n", encoding="utf-8")
        (repo / "LeanQbe" / "T").mkdir(parents=True)
        (repo / "LeanQbe" / "T" / "IL.lean").write_text("module\n", encoding="utf-8")
        (repo / "LeanQbe" / "T" / "Examples" / "Kissat").mkdir(parents=True)
        (repo / "LeanQbe" / "T" / "Examples" / "Kissat" / "FullFidelityStep7.lean").write_text(
            "module\nimport LeanQbe.T.IL\n", encoding="utf-8"
        )
        (repo / "LeanQbe" / "T" / "Amd64").mkdir(parents=True)
        (repo / "LeanQbe" / "T" / "Amd64" / "KissatPlainCert1.lean").write_text(
            "module\nimport LeanQbe.T.Examples.Kissat.FullFidelityStep7\n",
            encoding="utf-8",
        )
        (repo / "LeanQbe" / "T" / "Leaf.lean").write_text(
            "module\nimport LeanQbe.T.IL\n", encoding="utf-8"
        )
        (repo / "LeanQbeTest" / "T").mkdir(parents=True)
        (repo / "LeanQbeTest" / "T" / "LeafTest.lean").write_text(
            "module\nimport LeanQbe.T.Leaf\n", encoding="utf-8"
        )
        _git(repo, "add", "-A")
        _git(repo, "commit", "-m", "base")
        base_sha = _git(repo, "rev-parse", "leanqbe/main")
        return repo, base_sha

    def test_classify_branch_lanes(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            repo, base_sha = self._init_lane_test_repo(Path(td))

            _git(repo, "checkout", "-b", "speedup_p0_infra", base_sha)
            _commit_file(repo, "scripts/fast.py", "x = 1\n", "infra")

            _git(repo, "checkout", "-b", "c0d_bench", base_sha)
            _commit_file(repo, "bench/kissat/c0d.py", "y = 1\n", "bench")

            _git(repo, "checkout", "-b", "doc_only", base_sha)
            _commit_file(repo, "README.md", "updated\n", "docs")

            _git(repo, "checkout", "-b", "lakefile_only", base_sha)
            _commit_file(repo, "lakefile.toml", "name = \"leanqbe\"\n# ok\n", "lakefile")

            _git(repo, "checkout", "-b", "hub_only", base_sha)
            _commit_file(repo, "LeanQbe.lean", "module\n-- hub\n", "hub")

            _git(repo, "checkout", "-b", "test_dir_only", base_sha)
            _commit_file(repo, "test/run.sh", "#!/usr/bin/env bash\n", "test script")

            _git(repo, "checkout", "-b", "disjoint_leaf", base_sha)
            _commit_file(
                repo,
                "LeanQbeTest/T/NewSmallTest.lean",
                "module\nimport LeanQbe.T.Leaf\n",
                "new small leaf test",
            )

            _git(repo, "checkout", "-b", "disjoint_lean_leaf", base_sha)
            _commit_file(repo, "LeanQbe/T/Leaf.lean", "module\n-- ok\n", "leaf edit")

            _git(repo, "checkout", "-b", "step7_heavy", base_sha)
            _commit_file(
                repo,
                "LeanQbe/T/Examples/Kissat/FullFidelityStep7.lean",
                "module\n-- step7\n",
                "step7 kissat c0",
            )

            _git(repo, "checkout", "-b", "cert_slice_heavy", base_sha)
            _commit_file(
                repo,
                "LeanQbe/T/Amd64/KissatPlainCert1.lean",
                "module\n-- slice\n",
                "cert slice",
            )

            _git(repo, "checkout", "-b", "core_il_heavy", base_sha)
            _commit_file(repo, "LeanQbe/T/IL.lean", "module\n-- il\n", "core il")

            _git(repo, "checkout", "-b", "mixed_infra_and_core", base_sha)
            _commit_file(repo, "scripts/helper.py", "z = 1\n", "script")
            _commit_file(repo, "LeanQbe/T/IL.lean", "module\n-- il2\n", "plus core")

            _git(repo, "checkout", "leanqbe/main")

            for br in (
                "speedup_p0_infra",
                "c0d_bench",
                "doc_only",
                "lakefile_only",
                "hub_only",
                "test_dir_only",
            ):
                cls = mt.classify_branch(repo, base_sha, br)
                self.assertEqual(cls["lane"], "infra_fast", (br, cls))
                self.assertEqual(cls["priority"], 0, br)
                self.assertEqual(cls["build_lane"], 1, br)

            for br in ("disjoint_leaf", "disjoint_lean_leaf"):
                cls = mt.classify_branch(repo, base_sha, br)
                self.assertEqual(cls["lane"], "disjoint_fast", (br, cls))
                self.assertEqual(cls["priority"], 1, br)
                self.assertEqual(cls["build_lane"], 1, br)
                self.assertLessEqual(cls["rdeps_count"], 25)
                self.assertEqual(cls["cert_slices"], [])

            for br in (
                "step7_heavy",
                "cert_slice_heavy",
                "core_il_heavy",
                "mixed_infra_and_core",
            ):
                cls = mt.classify_branch(repo, base_sha, br)
                self.assertEqual(cls["lane"], "core_heavy", (br, cls))
                self.assertEqual(cls["priority"], 2, br)
                self.assertEqual(cls["build_lane"], 2, br)

            # Explicit rdeps threshold (> 25) & cert-slice rdeps promote to core_heavy.
            over_cap = mt.classify_branch(
                repo,
                base_sha,
                "disjoint_lean_leaf",
                changed_files=["LeanQbe/T/Leaf.lean"],
                rdeps_mods=[f"LeanQbe.T.Mod{i}" for i in range(26)],
            )
            self.assertEqual(over_cap["lane"], "core_heavy")
            cert_dep = mt.classify_branch(
                repo,
                base_sha,
                "disjoint_lean_leaf",
                changed_files=["LeanQbe/T/Leaf.lean"],
                rdeps_mods=["LeanQbe.T.Leaf", "LeanQbe.T.Amd64.KissatPlainCert2"],
            )
            self.assertEqual(cert_dep["lane"], "core_heavy")

    def test_classify_real_repo_speedup_and_step7_commits(self) -> None:
        needed = ("4fa7421b", "55281008", "9fdf1370", "176dbe49")
        for rev in needed:
            ok = subprocess.run(
                ["git", "-C", str(REPO_ROOT), "cat-file", "-e", f"{rev}^{{commit}}"],
                capture_output=True,
                check=False,
            )
            if ok.returncode != 0:
                self.skipTest(f"commit {rev} not present in repo")

        for rev in ("55281008", "9fdf1370"):
            cls = mt.classify_branch(REPO_ROOT, "4fa7421b", rev)
            self.assertEqual(cls["lane"], "infra_fast", (rev, cls))
            self.assertEqual(cls["priority"], 0)
        heavy_cls = mt.classify_branch(REPO_ROOT, "176dbe49", "4fa7421b")
        self.assertEqual(heavy_cls["lane"], "core_heavy", heavy_cls)
        self.assertEqual(heavy_cls["priority"], 2)

    def test_infra_fast_first_ordering_and_hol_bypass_partition(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo, base_sha = self._init_lane_test_repo(root)

            _git(repo, "checkout", "-b", "step7_heavy", base_sha)
            _commit_file(
                repo,
                "LeanQbe/T/Examples/Kissat/FullFidelityStep7.lean",
                "module\n-- step7 edit\n",
                "step7 heavy",
            )
            _commit_file(repo, "shared_doc.md", "from step7\n", "touch shared doc")

            _git(repo, "checkout", "-b", "speedup_p0_infra", base_sha)
            _commit_file(repo, "scripts/p0.py", "ok = True\n", "p0 infra")

            _git(repo, "checkout", "-b", "c0d_bench", base_sha)
            _commit_file(repo, "bench/kissat/c0d.py", "fast = 1\n", "c0d bench")

            _git(repo, "checkout", "-b", "doc_only", base_sha)
            _commit_file(repo, "README.md", "updated docs\n", "doc only")

            _git(repo, "checkout", "-b", "disjoint_fast_pr", base_sha)
            _commit_file(repo, "LeanQbe/T/Leaf.lean", "module\n-- leaf\n", "leaf")

            # Conflicting fast PR touching same file as step7_heavy (cannot bypass HoL).
            _git(repo, "checkout", "-b", "doc_conflicts_heavy", base_sha)
            _commit_file(repo, "shared_doc.md", "from doc conflict\n", "conflict")

            _git(repo, "checkout", "leanqbe/main")

            queue = ["step7_heavy", "speedup_p0_infra", "c0d_bench", "doc_only"]
            part = mt.partition_lanes(repo, "leanqbe/main", queue)
            self.assertEqual(
                [c.branch for c in part["ordered"]],
                ["speedup_p0_infra", "c0d_bench", "doc_only", "step7_heavy"],
            )
            self.assertEqual(
                [c.branch for c in part["fast_batch"]],
                ["speedup_p0_infra", "c0d_bench", "doc_only"],
            )
            self.assertEqual([c.branch for c in part["heavy_batch"]], ["step7_heavy"])
            self.assertEqual(part["deferred_to_heavy"], [])

            # Mixed queue with disjoint_fast + conflicting infra PR:
            mixed = [
                "step7_heavy",
                "disjoint_fast_pr",
                "speedup_p0_infra",
                "doc_conflicts_heavy",
                "c0d_bench",
            ]
            part_mix = mt.partition_lanes(repo, "leanqbe/main", mixed)
            self.assertEqual(
                [c.branch for c in part_mix["ordered"]],
                [
                    "speedup_p0_infra",
                    "doc_conflicts_heavy",
                    "c0d_bench",
                    "disjoint_fast_pr",
                    "step7_heavy",
                ],
            )
            self.assertEqual(
                [c.branch for c in part_mix["fast_batch"]],
                ["speedup_p0_infra", "c0d_bench", "disjoint_fast_pr"],
            )
            self.assertEqual(
                {c.branch for c in part_mix["heavy_batch"]},
                {"step7_heavy", "doc_conflicts_heavy"},
            )
            self.assertEqual(
                [d["branch"] for d in part_mix["deferred_to_heavy"]],
                ["doc_conflicts_heavy"],
            )
            self.assertEqual(
                part_mix["deferred_to_heavy"][0]["reason"],
                "conflicts_with_core_heavy",
            )

            # Dry-run CLI --lane auto executes fast before heavy with 0 ref mutations.
            cli_res = subprocess.run(
                [
                    sys.executable,
                    "-B",
                    str(SCRIPTS_DIR / "merge_train.py"),
                    "--root",
                    str(repo),
                    "--base",
                    "leanqbe/main",
                    "--lane",
                    "auto",
                    "--dry-run",
                    "--json",
                    *queue,
                ],
                capture_output=True,
                text=True,
                timeout=30,
                check=True,
            )
            rep = json.loads(cli_res.stdout)
            self.assertTrue(rep["ok"], rep)
            self.assertEqual(rep["lane_mode"], "auto")
            self.assertEqual(
                [c["branch"] for c in rep["accepted"]],
                ["speedup_p0_infra", "c0d_bench", "doc_only", "step7_heavy"],
            )
            self.assertEqual(rep["lanes"]["fast"]["build_lane"], 1)
            self.assertEqual(rep["lanes"]["heavy"]["build_lane"], 2)
            self.assertEqual(_git(repo, "rev-parse", "leanqbe/main"), base_sha)

            # `--lane fast` processes ONLY fast_batch and defers step7_heavy.
            rep_fast = mt.run_merge_train(
                repo, queue, base_ref="leanqbe/main", dry_run=True, lane="fast"
            )
            self.assertEqual(
                [c["branch"] for c in rep_fast["accepted"]],
                ["speedup_p0_infra", "c0d_bench", "doc_only"],
            )
            self.assertEqual(rep_fast["deferred_heavy"], ["step7_heavy"])

            # `--lane heavy` processes ONLY heavy_batch and defers fast_batch.
            rep_heavy = mt.run_merge_train(
                repo, queue, base_ref="leanqbe/main", dry_run=True, lane="heavy"
            )
            self.assertEqual(
                [c["branch"] for c in rep_heavy["accepted"]],
                ["step7_heavy"],
            )
            self.assertEqual(
                rep_heavy["deferred_fast"],
                ["speedup_p0_infra", "c0d_bench", "doc_only"],
            )

    def test_hol_bypass_lands_fast_even_if_heavy_fails(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo, base_sha = self._init_lane_test_repo(root)

            land_log = root / "fast_land_calls.log"
            (repo / "scripts" / "fast_land.sh").write_text(
                "#!/usr/bin/env bash\n"
                f"echo \"lane=${{CHECK_BUILD_LANE:-unset}} args=$*\" >> '{land_log}'\n",
                encoding="utf-8",
            )
            os.chmod(repo / "scripts" / "fast_land.sh", 0o755)
            _git(repo, "add", "scripts/fast_land.sh")
            _git(repo, "commit", "-m", "add fast_land stub")
            base_sha = _git(repo, "rev-parse", "leanqbe/main")

            # step7_heavy passes merge-tree, but breaks check_firewall in staging.
            _git(repo, "checkout", "-b", "step7_heavy", base_sha)
            _commit_file(
                repo,
                "LeanQbe/T/Examples/Kissat/FullFidelityStep7.lean",
                "module\n-- broken heavy\n",
                "step7 heavy",
            )
            _commit_file(
                repo,
                "scripts/check_firewall.py",
                "import sys; sys.exit(1)\n",
                "break firewall on heavy branch",
            )

            _git(repo, "checkout", "-b", "speedup_p0_infra", base_sha)
            _commit_file(repo, "scripts/p0.py", "ok = 1\n", "p0")

            _git(repo, "checkout", "-b", "c0d_bench", base_sha)
            _commit_file(repo, "bench/kissat/c0d.py", "ok = 2\n", "c0d")

            _git(repo, "checkout", "-b", "doc_only", base_sha)
            _commit_file(repo, "README.md", "docs v2\n", "doc")

            _git(repo, "checkout", "leanqbe/main")
            wt = root / "staging-wt"
            with mock.patch.object(
                mt,
                "execute_lake_build",
                return_value={"status": "pass", "targets": []},
            ):
                rep = mt.run_merge_train(
                    repo,
                    ["step7_heavy", "speedup_p0_infra", "c0d_bench", "doc_only"],
                    base_ref="leanqbe/main",
                    worktree=wt,
                    dry_run=False,
                    execute=True,
                    fast_land_skip_tests=True,
                    lane="auto",
                )
            self.assertTrue(rep["ok"], rep)
            self.assertEqual(
                [c["branch"] for c in rep["accepted"]],
                ["speedup_p0_infra", "c0d_bench", "doc_only"],
            )
            self.assertEqual([e["branch"] for e in rep["ejected"]], ["step7_heavy"])
            self.assertEqual(rep["lanes"]["fast"]["status"], "pass")
            self.assertEqual(rep["lanes"]["heavy"]["status"], "fail")
            # Fast batch already landed on leanqbe/main despite heavy failure!
            self.assertNotEqual(_git(repo, "rev-parse", "leanqbe/main"), base_sha)
            self.assertEqual(
                _git(repo, "rev-parse", "leanqbe/main"),
                rep["lanes"]["fast"]["merged_sha"],
            )
            calls = land_log.read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(calls), 1)
            self.assertTrue(calls[0].startswith("lane=1 "))
            _git(repo, "worktree", "remove", "--force", str(wt))

    def test_two_lane_flock_nonblocking_fast_when_heavy_locked(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            heavy_lock = root / "heavy.lock"
            fast_prefix = root / "fast"
            hfd = os.open(heavy_lock, os.O_CREAT | os.O_RDWR, 0o666)
            try:
                fcntl.flock(hfd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                # Fast lane (lane=1) must acquire fast_0.lock immediately while heavy is held.
                with mt.lane_build_lock(
                    1,
                    lock_file=str(heavy_lock),
                    fast_lock_prefix=str(fast_prefix),
                ) as info:
                    self.assertTrue(info["locked"])
                    self.assertEqual(info["lane"], 1)
                    self.assertEqual(info["lock_path"], f"{fast_prefix}_0.lock")
                    self.assertEqual(os.environ.get("CHECK_BUILD_LANE"), "1")
                self.assertIsNone(os.environ.get("CHECK_BUILD_LANE"))
            finally:
                fcntl.flock(hfd, fcntl.LOCK_UN)
                os.close(hfd)

            with mt.lane_build_lock(
                2,
                lock_file=str(heavy_lock),
                fast_lock_prefix=str(fast_prefix),
            ) as info2:
                self.assertTrue(info2["locked"])
                self.assertEqual(info2["lane"], 2)
                self.assertEqual(info2["lock_path"], str(heavy_lock))
                self.assertEqual(os.environ.get("CHECK_BUILD_LANE"), "2")
            self.assertIsNone(os.environ.get("CHECK_BUILD_LANE"))

    def test_cas_guard_and_no_premature_main_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo, base_sha = self._init_lane_test_repo(root)

            marker = root / "fast_land_called.txt"
            (repo / "scripts" / "fast_land.sh").write_text(
                "#!/usr/bin/env bash\n"
                f"echo \"$*\" >> '{marker}'\n",
                encoding="utf-8",
            )
            os.chmod(repo / "scripts" / "fast_land.sh", 0o755)
            _git(repo, "add", "scripts/fast_land.sh")
            _git(repo, "commit", "-m", "add fast_land")
            base_sha = _git(repo, "rev-parse", "leanqbe/main")

            _git(repo, "checkout", "-b", "pr-good", base_sha)
            good_sha = _commit_file(repo, "README.md", "good\n", "good doc")

            _git(repo, "checkout", "-b", "pr-bad-fw", base_sha)
            _commit_file(
                repo,
                "scripts/check_firewall.py",
                "import sys; sys.exit(1)\n",
                "fail firewall",
            )

            _git(repo, "checkout", "--detach", base_sha)
            wt = root / "staging-wt"

            # 1. Stage mode (execute=False) never mutates refs/heads/leanqbe/main.
            rep_stage = mt.run_merge_train(
                repo,
                ["pr-good"],
                base_ref="leanqbe/main",
                worktree=wt,
                dry_run=False,
                execute=False,
            )
            self.assertTrue(rep_stage["ok"], rep_stage)
            self.assertEqual(_git(repo, "rev-parse", "refs/heads/leanqbe/main"), base_sha)
            self.assertFalse(marker.exists())

            # 2. Failed staging validation never mutates main or calls fast_land.sh.
            rep_fail = mt.run_merge_train(
                repo,
                ["pr-bad-fw"],
                base_ref="leanqbe/main",
                worktree=wt,
                dry_run=False,
                execute=True,
            )
            self.assertFalse(rep_fail["ok"])
            self.assertEqual(_git(repo, "rev-parse", "refs/heads/leanqbe/main"), base_sha)
            self.assertFalse(marker.exists())

            # 3. Direct CAS guard rejects stale expected_old_sha and accepts exact match.
            cas_bad = mt.cas_update_ref(repo, "leanqbe/main", good_sha, "0" * 40)
            self.assertEqual(cas_bad["status"], "fail")
            self.assertEqual(cas_bad["reason"], "cas_mismatch")
            self.assertEqual(_git(repo, "rev-parse", "refs/heads/leanqbe/main"), base_sha)

            # 4. Concurrent advance before landing aborts execute=True with cas_mismatch.
            orig_stage = mt.stage_and_verify_subset

            def race_during_stage(*args, **kwargs):
                res = orig_stage(*args, **kwargs)
                # Simulate another lander advancing leanqbe/main during staging.
                _git(repo, "update-ref", "refs/heads/leanqbe/main", good_sha, base_sha)
                return res

            with mock.patch.object(mt, "stage_and_verify_subset", side_effect=race_during_stage):
                rep_race = mt.run_merge_train(
                    repo,
                    ["pr-good"],
                    base_ref="leanqbe/main",
                    worktree=wt,
                    dry_run=False,
                    execute=True,
                )
            self.assertFalse(rep_race["ok"])
            self.assertEqual(rep_race["fast_land"]["reason"], "cas_mismatch")
            self.assertFalse(marker.exists())
            self.assertEqual(_git(repo, "rev-parse", "refs/heads/leanqbe/main"), good_sha)
            _git(repo, "worktree", "remove", "--force", str(wt))


if __name__ == "__main__":
    unittest.main()
