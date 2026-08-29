from __future__ import annotations

import io
import sqlite3
import tempfile
import unittest
from contextlib import closing, redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from src.toy_apollo.state_cli import main, render_worklist
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore


class StateCliTests(unittest.TestCase):
    def _settings(self, root: Path) -> SimpleNamespace:
        runtime = root / "runtime"
        return SimpleNamespace(
            runtime_root=runtime,
            artifact_root=runtime,
            workspace_root=root,
            state_db_file=root / "runtime-artifacts" / "state.sqlite3",
            phase2_prompt_packs_dir=runtime / "phase2_prompt_packs",
        )

    def test_missing_status_is_fail_closed_and_does_not_create_database(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            output = io.StringIO()
            with redirect_stdout(output):
                code = main(["status", "thm_1_1", "--no-refresh"], settings)
            self.assertEqual(code, 2)
            self.assertIn("STATE_DB_STATUS=missing_not_created", output.getvalue())
            self.assertFalse(settings.state_db_file.exists())

    def test_status_refreshes_local_and_github_by_default(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            store = WorkspaceStateStore(settings.state_db_file)
            subject = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={"ProbabilityTheory/chapter_01/thm_1_1.lean": "theorem t : True := by trivial\n"},
                primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
                source_repo="kenneth",
                layout="kenneth",
            )
            store.upsert_subject(subject)
            store.set_task_head(task_id="thm_1_1", role="kenneth_main", subject_id=subject.subject_id)
            refresh_payload = {"local": {"errors": []}, "remote": {"errors": []}}
            output = io.StringIO()
            with patch(
                "src.toy_apollo.state_cli.refresh_workspace_state",
                return_value=refresh_payload,
            ) as refresh, redirect_stdout(output):
                code = main(["status", "thm_1_1"], settings)

            self.assertEqual(code, 0)
            refresh.assert_called_once()
            self.assertTrue(refresh.call_args.kwargs["refresh_remote"])
            self.assertEqual(refresh.call_args.kwargs["task_ids"], ["thm_1_1"])
            self.assertIn("REFRESH=ok", output.getvalue())

    def test_cordis_status_refreshes_only_local_catalog_roles(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            settings.profile = "cordis"
            WorkspaceStateStore(
                settings.state_db_file,
                review_profile="cordis",
            ).initialize()
            catalog = object()
            refresh_payload = {
                "local": {"cordis_current": 1, "errors": []},
                "remote": None,
            }
            output = io.StringIO()
            with (
                patch("src.toy_apollo.state_cli.load_catalog", return_value=catalog),
                patch(
                    "src.toy_apollo.state_cli.refresh_workspace_state",
                    return_value=refresh_payload,
                ) as refresh,
                redirect_stdout(output),
            ):
                code = main(["status", "def_2"], settings)

            self.assertEqual(code, 0)
            refresh.assert_called_once()
            self.assertFalse(refresh.call_args.kwargs["refresh_remote"])
            self.assertIs(refresh.call_args.kwargs["catalog"], catalog)
            self.assertIn("CORDIS_CURRENT=missing", output.getvalue())
            self.assertNotIn("MAT_MAIN=", output.getvalue())

    def test_no_refresh_uses_database_without_repository_calls(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            WorkspaceStateStore(settings.state_db_file).initialize()
            output = io.StringIO()
            with patch("src.toy_apollo.state_cli.refresh_workspace_state") as refresh, redirect_stdout(output):
                code = main(["worklist", "--no-refresh"], settings)
            self.assertEqual(code, 0)
            refresh.assert_not_called()
            self.assertIn("TASK\tACTIONS", output.getvalue())

            self.assertIn("CANDIDATE_MAINTENANCE_IS_CATALOG_FAILURE\tfalse", output.getvalue())

    def test_worklist_separates_authoritative_completion_from_candidate_maintenance(self):
        output = render_worklist(
            [{"task_id": "def_10_2", "actions": ["review_scope_rebind_required"]}],
            completion={
                "status": "pass",
                "all_required_pass": True,
                "compatible_pass_found": 452,
                "catalog_expected": 452,
                "required_incomplete": 0,
            },
        )

        self.assertIn("AUTHORITATIVE_CATALOG_COMPLETION\tPASS", output)
        self.assertIn("CATALOG_COMPATIBLE_PASS\t452/452", output)
        self.assertIn("REQUIRED_INCOMPLETE\t0", output)
        self.assertIn("CANDIDATE_MAINTENANCE\t1", output)
        self.assertIn("CANDIDATE_MAINTENANCE_IS_CATALOG_FAILURE\tfalse", output)
        self.assertIn("def_10_2\treview_scope_rebind_required", output)

    def test_validate_reports_legacy_schema_without_modifying_database(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings = self._settings(Path(tmp))
            settings.state_db_file.parent.mkdir(parents=True)
            with closing(sqlite3.connect(settings.state_db_file)) as connection:
                with connection:
                    connection.execute("CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT NOT NULL)")
                    connection.execute("INSERT INTO meta(key, value) VALUES('schema_version', '1')")
            before = settings.state_db_file.read_bytes()
            output = io.StringIO()
            with (
                patch("src.toy_apollo.state_cli.load_catalog", return_value=object()),
                patch(
                    "src.toy_apollo.state_cli.rebuild_invariants",
                    side_effect=sqlite3.OperationalError("no such table: catalog_tasks"),
                ),
                redirect_stdout(output),
            ):
                code = main(["state", "validate", "--json"], settings)

            self.assertEqual(code, 2)
            self.assertIn('"database_status": "legacy_schema_rebuild_required"', output.getvalue())
            self.assertEqual(settings.state_db_file.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
