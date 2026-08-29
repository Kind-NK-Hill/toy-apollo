from __future__ import annotations

import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from src.toy_apollo.core.settings import (
    DEFAULT_RUNTIME_ROOT,
    canonical_state_path,
    get_settings,
    profile_spec,
)
from src.toy_apollo.state_store import canonical_state_path as state_store_canonical_state_path


class SettingsTests(unittest.TestCase):
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
            DEFAULT_RUNTIME_ROOT.parent / "toy-apollo-artifacts" / "state.sqlite3",
        )

    def test_absolute_environment_overrides_remain_supported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            runtime = root / "runtime"
            artifacts = root / "artifacts"
            with patch.dict(
                os.environ,
                {
                    "TOY_APOLLO_RUNTIME_ROOT": str(runtime),
                    "TOY_APOLLO_ARTIFACT_ROOT": str(artifacts),
                },
                clear=True,
            ):
                settings = get_settings()

            self.assertEqual(settings.runtime_root, runtime.resolve())
            self.assertEqual(settings.artifact_root, artifacts)
            self.assertEqual(settings.workspace_root, runtime.resolve().parent)

    def test_canonical_state_path_is_checkout_name_independent(self):
        with tempfile.TemporaryDirectory() as tmp:
            runtime = Path(tmp) / "renamed-checkout"
            expected = runtime.parent / "toy-apollo-artifacts" / "state.sqlite3"
            with patch.dict(
                os.environ,
                {"TOY_APOLLO_RUNTIME_ROOT": str(runtime)},
                clear=True,
            ):
                settings = get_settings()

            self.assertEqual(settings.state_db_file, expected)
            self.assertEqual(canonical_state_path(runtime), expected)
            self.assertEqual(state_store_canonical_state_path(runtime), expected)


if __name__ == "__main__":
    unittest.main()
