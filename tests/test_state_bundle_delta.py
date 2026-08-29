from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from src.toy_apollo.state_bundle_delta import analyze_current_mat_bundles, compare_bundles
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore


class BundleDeltaTests(unittest.TestCase):
    def _bundle(self, *, path: str, support: bool = False) -> SubjectBundle:
        files = {path: "theorem t : True := by trivial\n"}
        if support:
            files["support/helper.lean"] = "theorem helper : True := by trivial\n"
        return SubjectBundle.from_files(
            task_id="thm_1_1",
            files=files,
            primary_path=path,
            source_repo="mat",
            source_commit=path,
            layout="mat",
        )

    def test_primary_only_review_does_not_cover_support_bundle(self):
        reviewed = self._bundle(path="review/thm_1_1.lean")
        current = self._bundle(path="mat/thm_1_1.lean", support=True)
        comparison = compare_bundles(
            {
                "bundle_hash": reviewed.bundle_hash,
                "primary_hash": reviewed.primary_hash,
                "manifest_json": reviewed.manifest(),
            },
            {
                "bundle_hash": current.bundle_hash,
                "primary_hash": current.primary_hash,
                "manifest_json": current.manifest(),
            },
        )
        self.assertEqual(comparison.classification, "support_scope_unbound")

    def test_path_only_change_requires_receipted_rebind(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            reviewed = self._bundle(path="review/thm_1_1.lean")
            current = self._bundle(path="mat/thm_1_1.lean")
            store.upsert_subject(reviewed)
            store.upsert_subject(current)
            store.record_review(
                task_id="thm_1_1",
                subject_id=reviewed.subject_id,
                verdict="pass",
                proof_class="faithful",
                completion_class="complete",
                phase2_status="pass",
                evidence_path=Path(tmp) / "review.json",
                evidence_hash="review",
                authority_eligible=True,
                prompt_version=11,
                rubric_version=9,
            )
            store.set_task_head(
                task_id="thm_1_1", role="mat_main", subject_id=current.subject_id
            )

            before = analyze_current_mat_bundles(store)
            self.assertEqual(before["tasks"][0]["status"], "mechanical_rebind_required")

            store.record_transformation(
                task_id="thm_1_1",
                source_subject_id=reviewed.subject_id,
                target_subject_id=current.subject_id,
                transformation_kind="path_relocation",
                mechanical_status="pass",
                build_status="pass",
            )
            after = analyze_current_mat_bundles(store)
            self.assertEqual(after["tasks"][0]["status"], "validated_rebind")


if __name__ == "__main__":
    unittest.main()
