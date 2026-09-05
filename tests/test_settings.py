from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from formalization_engine.core.settings import (
    DEFAULT_ARTIFACT_REPOSITORY_NAME,
    DEFAULT_RUNTIME_ROOT,
    SettingsError,
    get_settings,
    profile_spec,
    resolve_profile,
)


class SettingsTests(unittest.TestCase):
    def test_unknown_profile_is_rejected_instead_of_selecting_mat(self):
        with patch.dict(os.environ, {"FORMALIZATION_ENGINE_PROFILE": "cordsi"}, clear=True):
            with self.assertRaisesRegex(SettingsError, "cordsi"):
                get_settings()
            with self.assertRaisesRegex(SettingsError, "cordsi"):
                resolve_profile()
        with self.assertRaisesRegex(SettingsError, "cordsi"):
            profile_spec("cordsi")

    def test_cordis_profile_resolves_isolated_paths_and_source_policy(self):
        for explicit_profile in (False, True):
            with self.subTest(explicit_profile=explicit_profile), tempfile.TemporaryDirectory() as tmp:
                workspace = Path(tmp)
                runtime = workspace / ("renamed-cordis" if explicit_profile else "cordis")
                policy_path = runtime / "data/task_catalog/catalog_policy_v1.json"
                policy_path.parent.mkdir(parents=True)
                policy = {
                    "schema_version": "cordis.task-catalog-policy.v1",
                    "profile": "cordis",
                    "source_kind": "cordis_modules",
                    "cordis_source": {
                        "commit": "a" * 40,
                        "plans_prefix": "plans",
                        "modules_prefix": "Cordis/Foundations",
                    },
                    "task_module_map": {"thm_4": "Cordis/Foundations/Test.lean"},
                }
                policy_path.write_text(json.dumps(policy), encoding="utf-8")
                original = policy_path.read_bytes()
                environment = {"FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime)}
                if explicit_profile:
                    environment["FORMALIZATION_ENGINE_PROFILE"] = "cordis"
                with patch.dict(os.environ, environment, clear=True):
                    settings = get_settings()
                self.assertEqual(settings.profile, "cordis")
                self.assertEqual(settings.artifact_root, workspace / "cordis-artifacts")
                self.assertEqual(settings.state_db_file, workspace / "cordis-artifacts/state.sqlite3")
                self.assertEqual(settings.canonical_lean_dir, runtime / "Cordis/Foundations")
                self.assertEqual(settings.canonical_lean_dir, settings.lean_module_dir)
                self.assertEqual(settings.supported_prompt_versions, (1,))
                self.assertEqual(settings.supported_rubric_version, 1)
                # Cordis uses the catalog's pinned module map, not a MAT manifest.
                self.assertIsNone(settings.reviewed_source)
                self.assertEqual(policy_path.read_bytes(), original)
                self.assertFalse(settings.artifact_root.exists())

                cli_environment = {
                    key: value for key, value in os.environ.items()
                    if not key.startswith(("FORMALIZATION_ENGINE_", "TOY_APOLLO_"))
                }
                cli_environment.update(environment)
                cli_environment["PYTHONPATH"] = str(Path(__file__).resolve().parents[1] / "src")
                result = subprocess.run(
                    [sys.executable, "-B", "-m", "formalization_engine", "--status"],
                    cwd=workspace, env=cli_environment, capture_output=True, text=True,
                    encoding="utf-8", timeout=30,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(str(settings.artifact_root), result.stdout)
                self.assertFalse(settings.artifact_root.exists())

    def test_legacy_review_versions_are_profile_scoped(self):
        self.assertEqual(profile_spec("mat").legacy_obligation_review_prompt_versions, (9, 10))
        self.assertEqual(profile_spec("cordis").legacy_obligation_review_prompt_versions, ())

    def test_default_runtime_root_is_independent_of_process_cwd(self):
        original_cwd = Path.cwd()
        with tempfile.TemporaryDirectory() as tmp:
            try:
                os.chdir(tmp)
                with patch.dict(os.environ, {}, clear=True):
                    settings = get_settings()
            finally:
                os.chdir(original_cwd)

        self.assertEqual(settings.runtime_root, DEFAULT_RUNTIME_ROOT)
        self.assertEqual(settings.workspace_root, DEFAULT_RUNTIME_ROOT.parent)
        self.assertEqual(
            settings.state_db_file,
            DEFAULT_RUNTIME_ROOT.parent / DEFAULT_ARTIFACT_REPOSITORY_NAME / "state.sqlite3",
        )

    def test_absolute_environment_overrides_remain_supported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = root / "runtime"
            artifacts = root / "artifacts"
            runtime.mkdir()
            with patch.dict(
                os.environ,
                {
                    "FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime),
                    "FORMALIZATION_ENGINE_ARTIFACT_ROOT": str(artifacts),
                },
                clear=True,
            ):
                settings = get_settings()

            self.assertEqual(settings.runtime_root, runtime.resolve())
            self.assertEqual(settings.artifact_root, artifacts)
            self.assertEqual(settings.workspace_root, runtime.resolve().parent)

    def test_state_database_override_must_belong_to_artifact_root(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = root / "runtime"
            runtime.mkdir()
            with patch.dict(
                os.environ,
                {
                    "FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime),
                    "FORMALIZATION_ENGINE_ARTIFACT_ROOT": str(root / "artifacts"),
                    "FORMALIZATION_ENGINE_STATE_DB": str(root / "elsewhere" / "state.sqlite3"),
                },
                clear=True,
            ):
                with self.assertRaises(SettingsError):
                    get_settings()

    def test_legacy_environment_names_are_not_runtime_fallbacks(self):
        with patch.dict(
            os.environ,
            {"TOY_APOLLO_RUNTIME_ROOT": "Z:/must-not-be-read"},
            clear=True,
        ):
            settings = get_settings()
        self.assertEqual(settings.runtime_root, DEFAULT_RUNTIME_ROOT)


if __name__ == "__main__":
    unittest.main()
