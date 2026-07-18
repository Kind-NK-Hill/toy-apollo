from __future__ import annotations

import io
import tempfile
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from src.toy_apollo.state_cli import main
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


if __name__ == "__main__":
    unittest.main()
