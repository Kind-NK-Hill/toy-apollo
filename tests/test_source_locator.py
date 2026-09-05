from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from formalization_engine.core.settings import get_settings
from formalization_engine.core.source_locator import SourceLocatorError
from tests.git_fixture_cleanup import remove_git_fixture_tree


class ReviewedSourceLocatorTests(unittest.TestCase):
    def _mat_policy_fixture(self, *, legacy: bool = False):
        workspace = Path(tempfile.mkdtemp(prefix="formalize-source-locator-"))
        self.addCleanup(remove_git_fixture_tree, workspace)
        repository = workspace / ("MAT3280-formalization-output" if legacy else "reviewed-source")
        repository.mkdir()
        (repository / "ProbabilityTheory").mkdir()
        (repository / "ProbabilityTheory/Test.lean").write_text(
            "theorem test : True := by trivial\n", encoding="utf-8"
        )
        (repository / "manifest_by_chapter.csv").write_text(
            "task_id,path\nthm_1_1,ProbabilityTheory/Test.lean\n", encoding="utf-8"
        )

        def git(*args: str) -> str:
            result = subprocess.run(
                ["git", "-c", "commit.gpgsign=false", "-c", f"core.hooksPath={workspace / 'no-hooks'}",
                 "-C", str(repository), *args],
                capture_output=True, text=True, check=True, timeout=30,
            )
            return result.stdout.strip()

        git("init")
        git("add", "ProbabilityTheory/Test.lean", "manifest_by_chapter.csv")
        git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-m", "source fixture")
        commit = git("rev-parse", "HEAD")
        runtime = workspace / "runtime"
        policy_path = runtime / "data/task_catalog/catalog_policy_v2.json"
        policy_path.parent.mkdir(parents=True)
        policy = {"schema_version": "task-catalog-policy.v1", "mat_source": {"commit": commit}} if legacy else {
            "schema_version": "task-catalog-policy.v2",
            "reviewed_source": {
                "repository_path": repository.name,
                "repository_identity": "fixture/reviewed-source",
                "commit": commit,
                "lean_prefix": "ProbabilityTheory",
                "manifest_path": "manifest_by_chapter.csv",
                "layout": "unified_probability_theory_v2",
                "source_role": "unified_reviewed_source",
            },
        }
        policy_path.write_text(json.dumps(policy), encoding="utf-8")
        return runtime, repository, policy_path, commit

    def test_cordis_native_source_rejects_reviewed_source_overrides(self):
        with tempfile.TemporaryDirectory() as tmp:
            runtime = Path(tmp) / "cordis"
            policy_path = runtime / "data/task_catalog/catalog_policy_v1.json"
            policy_path.parent.mkdir(parents=True)
            policy_path.write_text(json.dumps({
                "schema_version": "cordis.task-catalog-policy.v1",
                "profile": "cordis", "source_kind": "cordis_modules",
                "cordis_source": {"commit": "a" * 40},
                "task_module_map": {"thm_4": "Cordis/Foundations/Test.lean"},
            }), encoding="utf-8")
            with patch.dict(os.environ, {
                "FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime),
                "FORMALIZATION_ENGINE_REVIEWED_SOURCE_REPO": str(runtime),
            }, clear=True):
                with self.assertRaisesRegex(SourceLocatorError, "does not support reviewed-source overrides"):
                    get_settings()
            self.assertFalse((Path(tmp) / "cordis-artifacts").exists())

    def test_cordis_native_source_does_not_accept_unknown_or_mismatched_policy(self):
        policies = [
            {"schema_version": "unknown", "profile": "cordis", "cordis_source": {}},
            {"schema_version": "task-catalog-policy.v1", "mat_source": {"commit": "a" * 40}},
            {"schema_version": "cordis.task-catalog-policy.v1", "profile": "mat"},
            {"schema_version": "cordis.task-catalog-policy.v1", "profile": "cordis",
             "source_kind": "cordis_modules", "cordis_source": {}, "task_module_map": []},
        ]
        for policy in policies:
            with self.subTest(policy=policy), tempfile.TemporaryDirectory() as tmp:
                runtime = Path(tmp) / "cordis"
                policy_path = runtime / "data/task_catalog/catalog_policy_v1.json"
                policy_path.parent.mkdir(parents=True)
                policy_path.write_text(json.dumps(policy), encoding="utf-8")
                with patch.dict(os.environ, {"FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime)}, clear=True):
                    with self.assertRaises(SourceLocatorError):
                        get_settings()
                self.assertFalse((Path(tmp) / "cordis-artifacts").exists())

    def test_v2_policy_resolves_unified_exact_git_objects(self):
        runtime, repository, policy_path, commit = self._mat_policy_fixture()
        original = policy_path.read_bytes()
        with patch.dict(os.environ, {"FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime)}, clear=True):
            settings = get_settings()
        self.assertIsNotNone(settings.reviewed_source)
        locator = settings.reviewed_source.validate()
        self.assertEqual(locator.lean_prefix, "ProbabilityTheory")
        self.assertEqual(locator.manifest_path, "manifest_by_chapter.csv")
        self.assertEqual(locator.layout, "unified_probability_theory_v2")
        self.assertEqual(locator.source_role, "unified_reviewed_source")
        self.assertEqual(locator.repository, repository)
        self.assertEqual(locator.commit, commit)
        self.assertEqual(policy_path.read_bytes(), original)

    def test_v1_policy_adapter_remains_read_only_compatible(self):
        runtime, repository, policy_path, commit = self._mat_policy_fixture(legacy=True)
        original = policy_path.read_bytes()
        with patch.dict(
            os.environ,
            {"FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime)},
            clear=True,
        ):
            locator = get_settings().reviewed_source
        self.assertIsNotNone(locator)
        validated = locator.validate()
        self.assertEqual(validated.layout, "probability_theory_manifest_v1")
        self.assertEqual(validated.source_role, "legacy_mat_reviewed_source")
        self.assertEqual(validated.repository, repository)
        self.assertEqual(validated.commit, commit)
        self.assertEqual(policy_path.read_bytes(), original)

    def test_wrong_reviewed_source_repository_fails_closed(self):
        runtime, _, _, _ = self._mat_policy_fixture()
        with tempfile.TemporaryDirectory() as tmp:
            wrong = Path(tmp) / "not-a-repository"
            wrong.mkdir()
            with patch.dict(
                os.environ,
                {"FORMALIZATION_ENGINE_RUNTIME_ROOT": str(runtime),
                 "FORMALIZATION_ENGINE_REVIEWED_SOURCE_REPO": str(wrong)},
                clear=True,
            ):
                settings = get_settings()
            self.assertIsNotNone(settings.reviewed_source)
            with self.assertRaises(SourceLocatorError):
                settings.reviewed_source.validate()


if __name__ == "__main__":
    unittest.main()
