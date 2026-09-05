from pathlib import Path
from unittest import SkipTest, FunctionTestCase

from formalization_engine.state_reconcile import discover_catalog_git_subjects
from formalization_engine.state_store import (
    LEGACY_SUBJECT_SCHEMA,
    SUBJECT_SCHEMA_V2,
    SubjectBundle,
)
from formalization_engine.task_catalog import load_catalog


def test_subject_v2_is_distinct_without_changing_bundle_bytes() -> None:
    files = {
        "ProbabilityTheory/chapter_01/thm_1_1.lean":
            "theorem thm_1_1_fixture : True := by trivial\n"
    }
    legacy = SubjectBundle.from_files(
        task_id="thm_1_1",
        files=files,
        primary_path=next(iter(files)),
        source_repo="mat",
        source_commit="a" * 40,
        layout="mat",
    )
    unified = SubjectBundle.from_files(
        task_id="thm_1_1",
        files=files,
        primary_path=next(iter(files)),
        source_repo="ProbabilityTheoryFormalization",
        source_commit="b" * 40,
        layout="unified",
    )
    assert legacy.identity_schema == LEGACY_SUBJECT_SCHEMA
    assert unified.identity_schema == SUBJECT_SCHEMA_V2
    assert legacy.bundle_hash == unified.bundle_hash
    assert legacy.primary_hash == unified.primary_hash
    assert legacy.subject_id != unified.subject_id
    assert unified.as_dict()["schema"] == SUBJECT_SCHEMA_V2


def test_catalog_v2_git_subjects_use_subject_v2() -> None:
    runtime_root = Path(__file__).resolve().parents[1]
    if not (runtime_root / "data/task_catalog/catalog_policy_v2.json").is_file():
        raise SkipTest("requires private unified catalog policy and pinned source fixture")
    catalog = load_catalog(
        workspace_root=runtime_root.parent,
        runtime_root=runtime_root,
    )
    subjects = discover_catalog_git_subjects(
        runtime_root,
        ref=catalog.repository_commit,
        catalog=catalog,
        source_repo="ProbabilityTheoryFormalization",
        layout="unified",
        task_ids=["thm_1_1"],
    )
    assert tuple(subjects) == ("thm_1_1",)
    assert subjects["thm_1_1"].identity_schema == SUBJECT_SCHEMA_V2
    assert subjects["thm_1_1"].source_commit == catalog.repository_commit


def load_tests(loader, suite, pattern):
    suite.addTest(FunctionTestCase(test_subject_v2_is_distinct_without_changing_bundle_bytes))
    suite.addTest(FunctionTestCase(test_catalog_v2_git_subjects_use_subject_v2))
    return suite
