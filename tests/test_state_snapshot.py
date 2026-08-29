from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from src.toy_apollo.state_snapshot import create_dataset_snapshot
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore
from src.toy_apollo.task_catalog import (
    CatalogFamily,
    CatalogModule,
    CatalogTask,
    TaskCatalog,
)


def _catalog() -> TaskCatalog:
    task = CatalogTask(
        task_id="thm_1_1",
        family_id="thm_1_1",
        chapter=1,
        task_kind="Theorem_with_Proof",
        source_plan="chapter1",
        source_plan_path="plans/chapter1.json",
        source_hash="plan-hash",
        primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
        legacy_manifest_role="ledger_task_module",
        lifecycle_state="active",
    )
    family = CatalogFamily(
        family_id="thm_1_1",
        book_label="Theorem 1.1",
        family_kind="singleton",
        count_policy="one_task",
        members=(task.task_id,),
    )
    module = CatalogModule(
        path=task.primary_path,
        basename="thm_1_1.lean",
        module_name="ProbabilityTheory.chapter_01.thm_1_1",
        module_role="primary",
        owner_task_id=task.task_id,
        legacy_manifest_role="ledger_task_module",
        chapter=1,
    )
    return TaskCatalog(
        catalog_id="test-catalog-v1",
        catalog_name="test",
        toy_commit="toy",
        mat_commit="mat",
        manifest_sha256="manifest",
        plan_set_sha256="plans",
        policy_sha256="policy",
        tasks=(task,),
        families=(family,),
        modules=(module,),
        cohorts={"legacy": (task.task_id,)},
        restored_task_ids=(),
        role_migrations=(),
    )


class DatasetSnapshotTests(unittest.TestCase):
    def _state(self, path: Path, *, workspace: Path) -> WorkspaceStateStore:
        store = WorkspaceStateStore(path)
        store.persist_catalog(_catalog())
        source = SubjectBundle.from_files(
            task_id="thm_1_1",
            files={
                "ProbabilityTheory/chapter_01/thm_1_1.lean":
                    "theorem t : True := by trivial\n"
            },
            primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
            source_repo="mat",
            source_commit="mat",
            layout="mat",
        )
        target = SubjectBundle.from_files(
            task_id="thm_1_1",
            files={"chapter_01/thm_1_1.lean": "theorem t : True := by trivial\n"},
            primary_path="chapter_01/thm_1_1.lean",
            source_repo="mat",
            source_commit="mat",
            layout="mat-flat",
        )
        store.upsert_subject(source)
        store.upsert_subject(target)
        # Rebuild observation timestamps are deliberately different.  The
        # stable dataset contains the transformation identity and evidence,
        # not the time at which a rebuild re-observed that evidence.
        store.record_transformation(
            task_id=source.task_id,
            source_subject_id=source.subject_id,
            target_subject_id=target.subject_id,
            transformation_kind="path_relocation",
            mechanical_status="pass",
            build_status="pass",
            evidence_path=workspace / "receipt.json",
            evidence_hash="a" * 64,
        )
        store.set_task_head(
            task_id=target.task_id,
            role="mat_main",
            subject_id=target.subject_id,
            detail={"repo": str(workspace / "MAT3280-formalization-output")},
        )
        return store

    def test_snapshot_is_stable_across_rebuild_observation_times(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            first = self._state(workspace / "first.sqlite3", workspace=workspace)
            second = self._state(workspace / "second.sqlite3", workspace=workspace)

            snapshot_a = create_dataset_snapshot(
                first,
                invariants={"catalog_valid": True},
                workspace_root=workspace,
                persist=False,
            )
            snapshot_b = create_dataset_snapshot(
                second,
                invariants={"catalog_valid": True},
                workspace_root=workspace,
                persist=False,
            )

            self.assertEqual(snapshot_a.dataset_id, snapshot_b.dataset_id)
            self.assertNotIn("created_at", snapshot_a.payload["subjects"][0])
            self.assertNotIn("created_at", snapshot_a.payload["transformations"][0])
            self.assertNotIn("observed_at", snapshot_a.payload["task_heads"][0])
            self.assertFalse(
                any(
                    event["event_type"] == "subject_transformed"
                    for event in snapshot_a.payload["events"]
                )
            )

    def test_snapshot_registration_is_content_addressed(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            store = self._state(workspace / "state.sqlite3", workspace=workspace)
            output = workspace / "snapshots" / "dataset.json"

            snapshot = create_dataset_snapshot(
                store,
                invariants={"catalog_valid": True},
                workspace_root=workspace,
                output_path=output,
            )

            self.assertTrue(output.is_file())
            self.assertEqual(store.summary()["dataset_snapshots"], 1)
            self.assertEqual(
                json.loads(output.read_text(encoding="utf-8"))["dataset_id"],
                snapshot.dataset_id,
            )


if __name__ == "__main__":
    unittest.main()
