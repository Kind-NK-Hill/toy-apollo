from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from src.toy_apollo.state_catalog_sync import sync_active_catalog
from src.toy_apollo.state_reconcile import discover_catalog_worktree_subjects
from src.toy_apollo.state_store import WorkspaceStateStore
from src.toy_apollo.task_catalog import build_cordis_catalog


class StateCatalogSyncTests(unittest.TestCase):
    @staticmethod
    def _git(repo: Path, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()

    def test_sync_persists_catalog_and_stales_changed_reviewed_bundle(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            runtime = workspace / "cordis"
            runtime.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=runtime, check=True)
            subprocess.run(["git", "config", "user.email", "fixture@example.com"], cwd=runtime, check=True)
            subprocess.run(["git", "config", "user.name", "Fixture"], cwd=runtime, check=True)
            module_path = "Cordis/Foundations/EffectContext.lean"
            lean_path = runtime / module_path
            lean_path.parent.mkdir(parents=True)
            original = b"abbrev EffectContext (State : Type) := State\n"
            lean_path.write_bytes(original)
            subprocess.run(["git", "add", "-A"], cwd=runtime, check=True)
            subprocess.run(["git", "commit", "-qm", "fixture"], cwd=runtime, check=True)
            commit = self._git(runtime, "rev-parse", "HEAD")
            plan = json.dumps(
                [
                    {
                        "block_id": "def_2",
                        "type": "Definition",
                        "title": "Effect context",
                        "content": "Definition 2 fixture",
                        "dependencies": [],
                        "source_plan": "fixture",
                    }
                ]
            ).encode("utf-8")
            catalog = build_cordis_catalog(
                catalog_name="cordis-test",
                cordis_commit=commit,
                plan_documents={"plans/fixture_plan.json": plan},
                module_documents={module_path: original},
                task_module_map={"def_2": module_path},
            )
            store = WorkspaceStateStore(
                workspace / "cordis-artifacts" / "state.sqlite3",
                review_profile="cordis",
            )
            store.initialize()
            subject = discover_catalog_worktree_subjects(
                runtime,
                catalog=catalog,
                source_repo="cordis",
                layout="cordis",
            )["def_2"]
            store.upsert_subject(subject)
            store.set_task_head(
                task_id="def_2",
                role="cordis_reviewed",
                subject_id=subject.subject_id,
            )

            preview = sync_active_catalog(
                store=store,
                catalog=catalog,
                workspace_root=workspace,
                runtime_root=runtime,
                check_only=True,
            )
            self.assertFalse(preview["catalog_was_present"])
            self.assertEqual(preview["reviewed_exact_preserved"], ["def_2"])
            with store._connection(write=False) as connection:
                self.assertEqual(
                    connection.execute("SELECT COUNT(*) FROM catalog_versions").fetchone()[0],
                    0,
                )

            applied = sync_active_catalog(
                store=store,
                catalog=catalog,
                workspace_root=workspace,
                runtime_root=runtime,
            )
            self.assertEqual(applied["current_heads_written"], 1)
            with store._connection(write=False) as connection:
                roles = {
                    str(row[0])
                    for row in connection.execute(
                        "SELECT role FROM task_heads WHERE task_id = 'def_2'"
                    ).fetchall()
                }
            self.assertEqual(roles, {"cordis_current", "cordis_reviewed"})

            lean_path.write_text("abbrev EffectContext (State : Type) := Unit\n", encoding="utf-8")
            changed = sync_active_catalog(
                store=store,
                catalog=catalog,
                workspace_root=workspace,
                runtime_root=runtime,
            )
            self.assertEqual(changed["reviewed_staled"], ["def_2"])
            with store._connection(write=False) as connection:
                freshness = connection.execute(
                    "SELECT freshness FROM task_heads WHERE task_id = 'def_2' AND role = 'cordis_reviewed'"
                ).fetchone()[0]
            self.assertEqual(freshness, "stale")


if __name__ == "__main__":
    unittest.main()
