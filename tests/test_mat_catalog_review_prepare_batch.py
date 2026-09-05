from __future__ import annotations

import json
import shutil
import unittest
import uuid
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from formalization_engine.state_store import SubjectBundle, sha256_file
from tools.mat_catalog_review_prepare_batch import (
    PrepareBatchError,
    load_prepare_batch_manifest,
    prepare_review_batch,
)
from tools.mat_catalog_review_prepare import PrepareError


class ExactReviewPrepareBatchTests(unittest.TestCase):
    commit = "3" * 40
    task_ids = ("thm_1_1", "thm_1_2")

    def setUp(self):
        self.root = (
            Path(__file__).resolve().parents[2]
            / "_analysis_tmp"
            / "test_mat_catalog_review_prepare_batch"
            / uuid.uuid4().hex
        )
        self.root.mkdir(parents=True)
        self.addCleanup(shutil.rmtree, self.root)
        self.workspace = self.root / "workspace"
        self.runtime = self.workspace / "ProbabilityTheoryFormalization"
        self.checkout = self.root / "checkout"
        self.builds = self.root / "exact-builds"
        self.output = self.root / "packs"
        self.runtime.mkdir(parents=True)
        self.checkout.mkdir()
        self.subjects: dict[str, SubjectBundle] = {}
        modules = []
        for task_id in self.task_ids:
            module = f"ProbabilityTheory.chapter_01.{task_id}"
            path = module.replace(".", "/") + ".lean"
            self.subjects[task_id] = SubjectBundle.from_files(
                task_id=task_id,
                files={path: f"theorem {task_id} : True := by trivial\n"},
                primary_path=path,
                source_repo="mat",
                source_commit=self.commit,
                layout="mat",
                subject_kind="catalog_git_bundle",
            )
            modules.append(
                SimpleNamespace(
                    owner_task_id=task_id,
                    module_role="primary",
                    module_name=module,
                )
            )
        self.catalog = SimpleNamespace(mat_commit=self.commit, modules=modules)
        self.specs: dict[str, Path] = {}
        for task_id in self.task_ids:
            spec = (self.root / "specs" / f"{task_id}.json").resolve()
            spec.parent.mkdir(parents=True, exist_ok=True)
            spec.write_text(json.dumps({"task_id": task_id}) + "\n", encoding="utf-8")
            self.specs[task_id] = spec
            receipt = self.builds / task_id / "exact_mat_build_receipt_v1.json"
            receipt.parent.mkdir(parents=True)
            receipt.write_text("{}\n", encoding="utf-8")
        items = []
        for task_id in self.task_ids:
            subject = self.subjects[task_id]
            items.append(
                {
                    "task_id": task_id,
                    "target_commit": self.commit,
                    "subject_id": subject.subject_id,
                    "bundle_hash": subject.bundle_hash,
                    "primary_hash": subject.primary_hash,
                    "spec_path": str(self.specs[task_id]),
                    "spec_sha256": sha256_file(self.specs[task_id]),
                    "spec_schema": "mat.catalog.review-supplement-spec.v1",
                    "canonical_dry_validation": "PASS",
                    "source_manifest_validation": "PASS",
                }
            )
        self.manifest = (self.root / "consolidated.json").resolve()
        self.manifest.write_text(
            json.dumps(
                {
                    "schema": "mat.catalog.exact-review-supplement-consolidated-manifest.v1",
                    "target_commit": self.commit,
                    "expected_unique_count": 2,
                    "counts": {"unique_tasks": 2},
                    "items": items,
                }
            ),
            encoding="utf-8",
        )

    def _git_text(self, _repo: Path, *args: str) -> str:
        if args[-1] in {"origin/main", "HEAD"}:
            return self.commit
        if "status" in args:
            return ""
        raise AssertionError(args)

    def _metadata(self, task_id: str) -> dict:
        receipt = (self.builds / task_id / "exact_mat_build_receipt_v1.json").resolve()
        return {
            "schema": "mat.catalog.exact-review-pack.v1",
            "task_id": task_id,
            "attempt": 1,
            "commit": self.commit,
            "build_receipt_mode": "reused_prebuilt",
            "build_checkout": str(self.checkout.resolve()),
            "prebuilt_exact_build_receipt_source": str(receipt),
            "prebuilt_exact_build_receipt_source_hash": sha256_file(receipt),
            "review_supplement_spec_file": str(self.specs[task_id]),
            "review_supplement_spec_hash": sha256_file(self.specs[task_id]),
            "expected_review_result_file": str(
                (self.output / task_id / "semantic_review_result_v1.json").resolve()
            ),
        }

    def _run(self, *, skip_existing: bool = True):
        with (
            patch(
                "tools.mat_catalog_review_prepare_batch.load_catalog",
                return_value=self.catalog,
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch._git_text",
                side_effect=self._git_text,
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch._catalog_subject",
                side_effect=lambda _catalog, *, task_id, mat_repo: self.subjects[task_id],
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch.validate_current_exact_build_receipt"
            ) as validate_receipt,
            patch(
                "tools.mat_catalog_review_prepare_batch._validate_pack"
            ) as validate_pack,
            patch(
                "tools.mat_catalog_review_prepare_batch._validate_prepare_complete_pack"
            ) as validate_prepared,
            patch(
                "tools.mat_catalog_review_prepare_batch.prepare_review",
                side_effect=lambda **kwargs: {
                    "metadata_file": str(
                        (kwargs["pack_dir"] / "mat_exact_subject.json").resolve()
                    )
                },
            ) as prepare,
        ):
            result = prepare_review_batch(
                manifest_path=self.manifest,
                exact_build_root=self.builds.resolve(),
                output_root=self.output,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                checkout=self.checkout,
                skip_existing=skip_existing,
            )
        return result, validate_receipt, validate_pack, validate_prepared, prepare

    def test_manifest_and_batch_skip_only_complete_revalidated_pack(self):
        commit, items = load_prepare_batch_manifest(self.manifest)
        self.assertEqual(commit, self.commit)
        self.assertEqual([item.task_id for item in items], list(self.task_ids))
        existing = self.output / self.task_ids[0]
        existing.mkdir(parents=True)
        (existing / "mat_exact_subject.json").write_text(
            json.dumps(self._metadata(self.task_ids[0])), encoding="utf-8"
        )
        result, validate_receipt, validate_pack, validate_prepared, prepare = self._run()
        self.assertEqual(result["requested"], 2)
        self.assertEqual(result["skipped_existing"], 1)
        self.assertEqual(result["prepared"], 1)
        self.assertEqual(validate_receipt.call_count, 2)
        validate_pack.assert_not_called()
        validate_prepared.assert_called_once()
        prepare.assert_called_once()
        kwargs = prepare.call_args.kwargs
        self.assertEqual(kwargs["task_id"], self.task_ids[1])
        self.assertEqual(kwargs["review_supplement_spec"], self.specs[self.task_ids[1]])
        self.assertEqual(
            kwargs["prebuilt_exact_build_receipt"],
            (self.builds / self.task_ids[1] / "exact_mat_build_receipt_v1.json").resolve(),
        )

    def test_partial_existing_pack_fails_without_prepare(self):
        (self.output / self.task_ids[0]).mkdir(parents=True)
        with self.assertRaisesRegex(PrepareBatchError, "partial"):
            self._run()

    def test_mismatched_existing_pack_fails_without_overwrite(self):
        existing = self.output / self.task_ids[0]
        existing.mkdir(parents=True)
        metadata = self._metadata(self.task_ids[0])
        metadata["review_supplement_spec_hash"] = "0" * 64
        metadata_path = existing / "mat_exact_subject.json"
        metadata_path.write_text(json.dumps(metadata), encoding="utf-8")
        before = metadata_path.read_bytes()
        with self.assertRaisesRegex(PrepareBatchError, "binding mismatch"):
            self._run()
        self.assertEqual(metadata_path.read_bytes(), before)

    def test_rerun_skips_first_pack_after_later_prepare_failure(self):
        def first_attempt(**kwargs):
            if kwargs["task_id"] == self.task_ids[1]:
                raise PrepareError("later task failed")
            pack_dir = kwargs["pack_dir"]
            pack_dir.mkdir(parents=True)
            metadata_path = pack_dir / "mat_exact_subject.json"
            metadata_path.write_text(
                json.dumps(self._metadata(kwargs["task_id"])), encoding="utf-8"
            )
            return {"metadata_file": str(metadata_path.resolve())}

        common = {
            "load_catalog": patch(
                "tools.mat_catalog_review_prepare_batch.load_catalog",
                return_value=self.catalog,
            ),
            "git_text": patch(
                "tools.mat_catalog_review_prepare_batch._git_text",
                side_effect=self._git_text,
            ),
            "subject": patch(
                "tools.mat_catalog_review_prepare_batch._catalog_subject",
                side_effect=lambda _catalog, *, task_id, mat_repo: self.subjects[task_id],
            ),
            "receipt": patch(
                "tools.mat_catalog_review_prepare_batch.validate_current_exact_build_receipt"
            ),
        }
        with (
            common["load_catalog"],
            common["git_text"],
            common["subject"],
            common["receipt"],
            patch(
                "tools.mat_catalog_review_prepare_batch.prepare_review",
                side_effect=first_attempt,
            ),
            self.assertRaisesRegex(PrepareBatchError, "later task failed"),
        ):
            prepare_review_batch(
                manifest_path=self.manifest,
                exact_build_root=self.builds.resolve(),
                output_root=self.output,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                checkout=self.checkout,
            )
        first_metadata = self.output / self.task_ids[0] / "mat_exact_subject.json"
        before = first_metadata.read_bytes()

        with (
            patch(
                "tools.mat_catalog_review_prepare_batch.load_catalog",
                return_value=self.catalog,
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch._git_text",
                side_effect=self._git_text,
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch._catalog_subject",
                side_effect=lambda _catalog, *, task_id, mat_repo: self.subjects[task_id],
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch.validate_current_exact_build_receipt"
            ),
            patch(
                "tools.mat_catalog_review_prepare_batch._validate_prepare_complete_pack"
            ) as validate_prepared,
            patch(
                "tools.mat_catalog_review_prepare_batch.prepare_review",
                return_value={
                    "metadata_file": str(
                        (
                            self.output
                            / self.task_ids[1]
                            / "mat_exact_subject.json"
                        ).resolve()
                    )
                },
            ) as prepare,
        ):
            result = prepare_review_batch(
                manifest_path=self.manifest,
                exact_build_root=self.builds.resolve(),
                output_root=self.output,
                workspace_root=self.workspace,
                runtime_root=self.runtime,
                checkout=self.checkout,
            )
        self.assertEqual(result["skipped_existing"], 1)
        self.assertEqual(result["prepared"], 1)
        validate_prepared.assert_called_once()
        self.assertEqual(prepare.call_args.kwargs["task_id"], self.task_ids[1])
        self.assertEqual(first_metadata.read_bytes(), before)


if __name__ == "__main__":
    unittest.main()
