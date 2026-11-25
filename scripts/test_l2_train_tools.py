#!/usr/bin/env python3
"""Unit & dry-run simulation tests for N9/N10/N11/N13 train tools."""

from __future__ import annotations

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

    def test_c0_memo_cache_roundtrip(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            cache = Path(td) / "c0_memo.json"
            key = "m7fidelity:abc123"
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

        fake_proc = subprocess.CompletedProcess(
            args=[], returncode=0, stdout="AXIOM_GROUP ok\n", stderr=""
        )
        with (
            mock.patch.object(l2, "systemd_scope_available", return_value=False),
            mock.patch.object(l2.subprocess, "run", return_value=fake_proc) as m_run,
        ):
            live = l2.run_axiom_audit(REPO_ROOT, mods, dry_run=False)
        self.assertEqual(live["status"], "pass")
        self.assertEqual(m_run.call_count, len(groups))
        self.assertEqual(len(live["chunk_runs"]), len(groups))

    def test_live_kernel_axiom_audit_cached_module(self) -> None:
        build_res = l2.execute_lake_build(
            REPO_ROOT, ["LeanQbeTest.T.Amd64FrameTest"]
        )
        self.assertEqual(build_res["status"], "pass", build_res)
        res = l2.run_axiom_audit(
            REPO_ROOT, ["LeanQbeTest.T.Amd64FrameTest"], dry_run=False
        )
        self.assertEqual(res["status"], "pass", res)
        self.assertIn("AXIOM_GROUP x64", str(res["stdout"]))


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


if __name__ == "__main__":
    unittest.main()
