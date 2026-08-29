from __future__ import annotations

import json
import hashlib
import subprocess
import unittest
import uuid
from contextlib import contextmanager
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from src.toy_apollo import state_boundary_delta_receipt as boundary_module
from src.toy_apollo.state_boundary_delta_receipt import (
    BOUNDARY_DELTA_SCHEMA,
    BoundaryDeltaReceiptError,
    _author_provenance,
    _bundle_content,
    _legacy_embedded_single_file_scope,
    _compare_files,
    _consumer_evidence,
    _resolve_registered_source_scope,
    _source_scope,
    build_verified_boundary_delta,
    emit_verified_boundary_delta_batch,
    load_boundary_batch_authority_manifest,
    validate_verified_boundary_delta,
)
from src.toy_apollo.state_transformation_receipt import FORBIDDEN_PATTERNS
from src.toy_apollo.state_review_apply_recovery import build_historical_review_apply_recovery
from src.toy_apollo.state_migration import (
    MigrationReport,
    discover_evidence_inventory,
    import_verified_boundary_delta_receipt,
)
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore, sha256_file
from src.toy_apollo.task_catalog import build_catalog
from tests import test_state_review_apply_recovery as _recovery_test_module
from tests.git_fixture_cleanup import remove_git_fixture_tree


class BoundaryDeltaReceiptTests(unittest.TestCase):
    @contextmanager
    def _temporary_root(self):
        # The managed Windows test sandbox applies an unusable ACL to
        # tempfile.TemporaryDirectory. A normal workspace child is writable.
        root = Path(__file__).resolve().parents[1] / f"_tmp_boundary_delta_{uuid.uuid4().hex}"
        root.mkdir()
        try:
            yield root
        finally:
            remove_git_fixture_tree(root)

    def _repo(self, root: Path, name: str, files: dict[str, str]) -> tuple[Path, str, SubjectBundle]:
        repo = root / name
        repo.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(["git", "config", "user.email", "fixture@example.invalid"], cwd=repo, check=True)
        subprocess.run(["git", "config", "user.name", "Fixture"], cwd=repo, check=True)
        for raw, content in files.items():
            path = repo / raw
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8", newline="\n")
        subprocess.run(["git", "add", "."], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-qm", "fixture"], cwd=repo, check=True)
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
        primary = sorted(files)[0]
        subject = SubjectBundle.from_files(
            task_id="thm_5_1", files=files, primary_path=primary,
            source_repo="mat" if name == "target" else "toy_apollo",
            source_commit=commit, layout="mat" if name == "target" else "toy",
            subject_kind="catalog_git_bundle" if name == "target" else "workspace_review_binding",
        )
        return repo, commit, subject

    def _fixture(self, root: Path, *, target_lean: str | None = None) -> dict[str, Path | str]:
        source_test = _recovery_test_module.HistoricalReviewApplyRecoveryTests()
        paths = source_test._write_pack(root)
        authority = build_historical_review_apply_recovery(
            pack_dir=paths["pack"], result_path=paths["result"], verify_path=paths["verify"],
            created_at="2026-08-08T00:00:00+00:00",
        )
        authority_path = paths["pack"] / "historical_review_apply_recovery_receipt_v1.json"
        authority_path.write_text(json.dumps(authority), encoding="utf-8")
        lean = "theorem recovered_fixture : True := by trivial\n"
        source_repo, _, source = self._repo(root, "source", {"Toy/Output/thm_5_1.lean": lean})
        target_text = target_lean if target_lean is not None else "/-- relocated docs -/\ntheorem recovered_fixture : True := by trivial\n"
        target_repo, target_commit, target = self._repo(root, "target", {"Probability/chapter_05/thm_5_1.lean": target_text})
        kenneth_repo, kenneth_commit, _ = self._repo(root, "kenneth", {"Unrelated.lean": "theorem unrelated : True := by trivial\n"})
        scope = {
            "schema_version": "toy-apollo.workspace-review-binding.v1",
            "tasks": [{
                "task_id": "thm_5_1", "binding_kind": "legacy_primary_scope_rebind",
                "basis_review": {"evidence_hash": authority["artifacts"]["result"]["sha256"], "primary_hash": source.primary_hash},
                "checks": {"build_status": "pass", "forbidden_scan_status": "pass", "support_scope_status": "pass", "mat_relocation_status": "pass"},
                "subjects": [{**{
                    "role": "toy_current", "source_repo": source.source_repo,
                    "source_commit": source.source_commit, "layout": source.layout,
                    "bundle_hash": source.bundle_hash, "primary_hash": source.primary_hash,
                    "primary_path": source.primary_path, "files": source.manifest(),
                }}],
            }]
        }
        scope_path = root / "scope.json"; scope_path.write_text(json.dumps(scope), encoding="utf-8")
        build = {
            "schema": "mat.catalog.exact-build.v1", "task_id": target.task_id,
            "commit": target_commit, "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash, "primary_hash": target.primary_hash,
            "primary_path": target.primary_path, "subject_files": target.manifest(),
            "success": True, "exit_code": 0,
            "forbidden_token_scan": {"exit_code": 0, "findings": {}},
            "lean_tree_equivalence": {"target_commit": target_commit, "build_checkout_clean": True, "changed_lean_files": []},
        }
        build_path = root / "target_build.json"; build_path.write_text(json.dumps(build), encoding="utf-8")
        policy = {
            "schema": "toy-apollo.boundary-delta-policy.v1", "task_id": "thm_5_1",
            "target_commit": target_commit, "module_rewrites": [],
            "file_pairs": [{"source": source.primary_path, "target": target.primary_path}],
        }
        policy_path = root / "policy.json"; policy_path.write_text(json.dumps(policy), encoding="utf-8")
        consumers = {
            "schema": "mat.catalog.direct-consumer-manifest.v1", "task_id": target.task_id,
            "commit": target_commit, "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash, "consumers": [],
        }
        consumers_path = root / "consumers.json"; consumers_path.write_text(json.dumps(consumers), encoding="utf-8")
        return {
            "authority": authority_path, "scope": scope_path, "source_repo": source_repo,
            "target_build": build_path, "target_repo": target_repo, "policy": policy_path,
            "consumers": consumers_path, "kenneth_repo": kenneth_repo, "kenneth_commit": kenneth_commit,
        }

    def _build(self, fixture: dict[str, Path | str]) -> dict:
        return build_verified_boundary_delta(
            source_authority_path=fixture["authority"], source_scope_path=fixture["scope"],
            source_repos=[fixture["source_repo"]], target_build_path=fixture["target_build"],
            target_repo=fixture["target_repo"], policy_path=fixture["policy"],
            consumer_manifest_path=fixture["consumers"], consumer_build_paths=[],
            kenneth_repo=fixture["kenneth_repo"], kenneth_commit=str(fixture["kenneth_commit"]),
            created_at="2026-08-08T00:00:00+00:00",
        )

    def _batch_task(self, root: Path, fixture: dict[str, Path | str]) -> Path:
        task_dir = root / "batch" / "thm_5_1"
        task_dir.mkdir(parents=True)
        policy_path = task_dir / "boundary_policy.json"
        policy_path.write_bytes(Path(fixture["policy"]).read_bytes())
        target_build = json.loads(Path(fixture["target_build"]).read_text(encoding="utf-8"))
        scope_payload = json.loads(Path(fixture["scope"]).read_text(encoding="utf-8"))
        authority_payload = json.loads(Path(fixture["authority"]).read_text(encoding="utf-8"))
        source = _source_scope(
            Path(fixture["scope"]), task_id="thm_5_1", authority=authority_payload,
        )
        kenneth_commit = str(fixture["kenneth_commit"])
        final_path = task_dir / "validated_boundary_delta_receipt_v1.json"
        manifest = {
            "schema": "toy-apollo.boundary-delta-input-manifest.v1",
            "task_id": "thm_5_1",
            "source_authority": {
                "path": str(fixture["authority"]),
                "sha256": sha256_file(Path(fixture["authority"])),
            },
            "source_scope": {
                "path": str(fixture["scope"]),
                "sha256": sha256_file(Path(fixture["scope"])),
                "schema": scope_payload["schema_version"],
                "scope_kind": "workspace_review_binding", "validation": "pass",
                "subject_id": source.subject_id, "bundle_hash": source.bundle_hash,
                "files": source.manifest(),
            },
            "policy": {"path": str(policy_path), "sha256": sha256_file(policy_path)},
            "direct_consumer_manifest": {
                "path": str(fixture["consumers"]),
                "sha256": sha256_file(Path(fixture["consumers"])),
            },
            "target_repository": {
                "path": str(fixture["target_repo"]),
                "commit": target_build["commit"],
                "subject_id": target_build["subject_id"],
                "bundle_hash": target_build["bundle_hash"],
                "primary_hash": target_build["primary_hash"],
                "files": target_build["subject_files"],
            },
            "kenneth_provenance": {
                "commit": kenneth_commit,
                "applicability": "not_applicable",
                "decision": "not_applicable_no_task_artifact",
                "matched_files": [],
            },
            "kenneth_author_decision": None,
            "planned_exact_build_receipts": {
                "target": {
                    "task_id": "thm_5_1", "receipt_path": str(fixture["target_build"]),
                    "sha256": sha256_file(Path(fixture["target_build"])),
                },
                "consumers": [],
            },
            "final_boundary_receipt": {"planned_path": str(final_path)},
        }
        (task_dir / "boundary_input_manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
        return task_dir

    def _emit_batch(self, task_dirs: list[Path], fixture: dict[str, Path | str]) -> dict:
        target_build = json.loads(Path(fixture["target_build"]).read_text(encoding="utf-8"))
        return emit_verified_boundary_delta_batch(
            task_dirs=task_dirs,
            source_repos=[Path(fixture["source_repo"])],
            target_repo=Path(fixture["target_repo"]),
            kenneth_repo=Path(fixture["kenneth_repo"]),
            expected_target_commit=target_build["commit"],
            expected_kenneth_commit=str(fixture["kenneth_commit"]),
        )

    def _authority_batch_fixture(
        self, root: Path, fixture: dict[str, Path | str], *, consumers: list[str] | None = None,
    ) -> tuple[Path, Path, Path, dict[str, object]]:
        task_dir = self._batch_task(root, fixture)
        old_input = task_dir / "boundary_input_manifest.json"
        manifest = json.loads(old_input.read_text(encoding="utf-8"))
        manifest["kenneth_provenance"] = {
            "applicability": "not_applicable", "repository": "kenneth",
            "commit": str(fixture["kenneth_commit"]), "matched_files": [], "files": [],
            "decision": "not_applicable_no_task_artifact",
        }
        consumer_ids = list(consumers or [])
        if consumer_ids:
            consumer_payload = json.loads(Path(fixture["consumers"]).read_text(encoding="utf-8"))
            consumer_payload["consumers"] = [
                {"task_id": task_id, "paths": ["Probability/missing.lean"]}
                for task_id in consumer_ids
            ]
            Path(fixture["consumers"]).write_text(json.dumps(consumer_payload), encoding="utf-8")
            manifest["direct_consumer_manifest"]["sha256"] = sha256_file(Path(fixture["consumers"]))
            manifest["planned_exact_build_receipts"]["consumers"] = [
                {"task_id": task_id, "receipt_path": f"old336/{task_id}.json"}
                for task_id in consumer_ids
            ]
        manifest["planned_exact_build_receipts"]["target"] = {
            "task_id": "thm_5_1", "receipt_path": "old336/thm_5_1.json",
        }
        reanchored = task_dir / "boundary_input_manifest_reanchored_v1.json"
        reanchored.write_text(json.dumps(manifest), encoding="utf-8")
        old_input.unlink()

        target = json.loads(Path(fixture["target_build"]).read_text(encoding="utf-8"))
        module = "Probability.chapter_05.thm_5_1"
        checkout = root.resolve()
        target.update({
            "campaign_id": "fixture", "created_at": "2026-08-08T00:00:00+00:00",
            "focused_build": {
                "command": ["lake", "build", module], "task_module": module,
                "task_module_in_combined_command": True, "task_modules": [module],
                "task_modules_in_combined_command": {module: True},
                "batch_index": 1, "batch_size": 1, "cwd": str(checkout),
                "exit_code": 0, "duration_seconds": 1.0, "stdout": "", "stderr": "",
            },
            "forbidden_token_scan": {
                "exit_code": 0, "findings": {}, "tokens": sorted(FORBIDDEN_PATTERNS),
            },
            "lean_tree_equivalence": {
                "build_commit": target["commit"], "target_commit": target["commit"],
                "changed_lean_files": [], "build_checkout_clean": True,
            },
        })
        central = root / "central"
        target_receipt = central / "thm_5_1" / "exact_mat_build_receipt_v1.json"
        target_receipt.parent.mkdir(parents=True)
        target_receipt.write_text(json.dumps(target), encoding="utf-8")
        subject = SubjectBundle.from_manifest(
            task_id="thm_5_1", files=target["subject_files"],
            primary_path=target["primary_path"], source_repo="mat",
            source_commit=target["commit"], layout="mat", subject_kind="catalog_git_bundle",
        )
        authority = {
            "schema": "mat.catalog.boundary97-policy-preflight-manifest.v1",
            "target_commit": target["commit"], "kenneth_commit": str(fixture["kenneth_commit"]),
            "counts": {"boundary_targets": 1, "unique_exact_build_closure_tasks": 1 + len(consumer_ids)},
            "items": [{
                "task_id": "thm_5_1", "pure_comparator": "pass",
                "overall_status": "ready_for_exact_build_evidence",
                "build_run": False, "final_receipt_emitted": False,
                "input_manifest": {"path": str(reanchored), "sha256": sha256_file(reanchored)},
                "policy": {"sha256": sha256_file(task_dir / "boundary_policy.json")},
                "direct_consumer_manifest": {"sha256": sha256_file(Path(fixture["consumers"]))},
                "direct_consumer_ids": consumer_ids, "direct_consumer_count": len(consumer_ids),
                "target_subject_id": target["subject_id"], "target_bundle_hash": target["bundle_hash"],
            }],
            "unique_planned_exact_build_tasks": ["thm_5_1", *consumer_ids],
        }
        authority_path = root / "authority.json"
        authority_path.write_text(json.dumps(authority), encoding="utf-8")
        context: dict[str, object] = {
            "commit": target["commit"], "subjects": {"thm_5_1": subject},
            "primary_modules": {"thm_5_1": module}, "owned_modules": {"thm_5_1": (module,)},
        }
        for consumer_id in consumer_ids:
            consumer_module = f"Probability.chapter_05.{consumer_id}"
            consumer_subject = SubjectBundle.from_files(
                task_id=consumer_id,
                files={"Probability/missing.lean": "theorem missing : True := by trivial\n"},
                primary_path="Probability/missing.lean", source_repo="mat",
                source_commit=target["commit"], layout="mat", subject_kind="catalog_git_bundle",
            )
            context["subjects"][consumer_id] = consumer_subject
            context["primary_modules"][consumer_id] = consumer_module
            context["owned_modules"][consumer_id] = (consumer_module,)
        return authority_path, central, task_dir, context

    def test_build_and_revalidate_without_sqlite(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root); receipt = self._build(fixture)
            self.assertEqual(receipt["schema"], BOUNDARY_DELTA_SCHEMA)
            self.assertEqual(receipt["public_declarations"]["status"], "unchanged")
            self.assertEqual(receipt["author_provenance"]["applicability"], "not_applicable")
            receipt_path = root / "receipt.json"; receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            validated, source, target = validate_verified_boundary_delta(
                receipt_path, source_repos=[fixture["source_repo"]], target_repo=fixture["target_repo"], kenneth_repo=fixture["kenneth_repo"],
            )
            self.assertEqual(validated["target_commit"], target.source_commit)
            self.assertNotEqual(source.bundle_hash, target.bundle_hash)

    def test_mathematical_or_public_contract_delta_fails_closed(self):
        for text in (
            "theorem recovered_fixture : False := by trivial\n",
            "theorem recovered_fixture : True := by exact True.intro\n",
        ):
            with self.subTest(text=text), self._temporary_root() as root:
                fixture = self._fixture(root, target_lean=text)
                with self.assertRaises(BoundaryDeltaReceiptError):
                    self._build(fixture)

    def test_tampered_source_authority_reference_fails_closed(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            scope = json.loads(Path(fixture["scope"]).read_text(encoding="utf-8"))
            scope["tasks"][0]["basis_review"]["evidence_hash"] = "0" * 64
            Path(fixture["scope"]).write_text(json.dumps(scope), encoding="utf-8")
            with self.assertRaises(BoundaryDeltaReceiptError):
                self._build(fixture)

    def test_cli_exposes_read_only_inspect_and_emit(self):
        result = subprocess.run(
            ["python", "tools/mat_verified_boundary_delta.py", "--help"],
            cwd=Path(__file__).resolve().parents[1], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("inspect", result.stdout)
        self.assertIn("emit", result.stdout)
        self.assertIn("emit-batch", result.stdout)

    def test_batch_emits_then_revalidates_and_skips_existing(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            task_dir = self._batch_task(root, fixture)
            emitted = self._emit_batch([task_dir], fixture)
            self.assertEqual((emitted["emitted"], emitted["failed"]), (1, 0))
            receipt_path = task_dir / "validated_boundary_delta_receipt_v1.json"
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(
                receipt["orchestration"]["input_manifest"]["sha256"],
                sha256_file(task_dir / "boundary_input_manifest.json"),
            )
            skipped = self._emit_batch([task_dir], fixture)
            self.assertEqual((skipped["emitted"], skipped["skipped_existing"], skipped["failed"]), (0, 1, 0))

    def test_real_boundary97_authority_manifest_parses_reanchored_inputs_dry(self):
        workspace = Path(__file__).resolve().parents[2]
        authority = workspace / "_analysis_tmp" / "boundary97_policy_preflight_manifest_mat11a7948f_final_20260808.json"
        if not authority.is_file():
            self.skipTest("private boundary-97 evidence is not included in the public source snapshot")
        payload, entries = load_boundary_batch_authority_manifest(
            authority, workspace_root=workspace,
            expected_sha256="bef49d50c374679062c2ddfd42812da85f6f7a3f3428d462809583842830e2a1",
            expected_target_commit="11a7948f752be3a6a55372c9c5fdba066a060c11",
            expected_kenneth_commit="e6387d4fd8005d627d2aec40d10f039ddb4e4b40",
        )
        self.assertEqual((len(entries), len(payload["unique_planned_exact_build_tasks"])), (97, 171))
        self.assertTrue(all(path.name == "boundary_input_manifest_reanchored_v1.json" for path, _item in entries.values()))
        with self.assertRaises(BoundaryDeltaReceiptError):
            load_boundary_batch_authority_manifest(
                authority, workspace_root=workspace, expected_sha256="0" * 64,
                expected_target_commit="11a7948f752be3a6a55372c9c5fdba066a060c11",
                expected_kenneth_commit="e6387d4fd8005d627d2aec40d10f039ddb4e4b40",
            )

    def test_authority_batch_uses_central_build_and_records_superseded_plan(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            authority, central, task_dir, context = self._authority_batch_fixture(root, fixture)
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                result = emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=Path(fixture["kenneth_repo"]),
                    expected_target_commit=json.loads(Path(fixture["target_build"]).read_text())["commit"],
                    expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority, authority_manifest_sha256=sha256_file(authority),
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual((result["emitted"], result["failed"]), (1, 0), result)
            receipt = json.loads((task_dir / "validated_boundary_delta_receipt_v1.json").read_text(encoding="utf-8"))
            override = receipt["orchestration"]["central_exact_build_override"]
            self.assertEqual(override["root"], str(central.resolve()))
            input_snapshot = Path(receipt["orchestration"]["input_manifest"]["path"])
            self.assertEqual(input_snapshot.parent.name, "input")
            self.assertEqual(input_snapshot.stem, receipt["orchestration"]["input_manifest"]["sha256"])

    def test_authority_batch_accepts_only_same_git_repository_clean_worktree_override(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            authority, central, task_dir, context = self._authority_batch_fixture(root, fixture)
            clean_worktree = root / "target_clean_worktree"
            subprocess.run(
                ["git", "worktree", "add", "--detach", str(clean_worktree),
                 json.loads(Path(fixture["target_build"]).read_text())["commit"]],
                cwd=Path(fixture["target_repo"]), check=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                result = emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=clean_worktree, kenneth_repo=Path(fixture["kenneth_repo"]),
                    expected_target_commit=json.loads(Path(fixture["target_build"]).read_text())["commit"],
                    expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority, authority_manifest_sha256=sha256_file(authority),
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual((result["emitted"], result["failed"]), (1, 0), result)
            receipt_path = task_dir / "validated_boundary_delta_receipt_v1.json"
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                validated, _source, target = validate_verified_boundary_delta(
                    receipt_path,
                    source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]),
                    kenneth_repo=Path(fixture["kenneth_repo"]),
                )
            self.assertEqual(validated["task_id"], "thm_5_1")
            self.assertEqual(target.source_commit, str(context["commit"]))

            unrelated_clone = root / "target_unrelated_clone"
            subprocess.run(
                ["git", "clone", "-q", str(Path(fixture["target_repo"])), str(unrelated_clone)],
                check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                with self.assertRaises(BoundaryDeltaReceiptError):
                    validate_verified_boundary_delta(
                        receipt_path,
                        source_repos=[Path(fixture["source_repo"])],
                        target_repo=unrelated_clone,
                        kenneth_repo=Path(fixture["kenneth_repo"]),
                    )

    def test_authority_batch_rejects_old_commit_missing_consumer_and_fake_absence(self):
        with self.subTest(case="old_commit"), self._temporary_root() as root:
            fixture = self._fixture(root)
            authority, central, task_dir, context = self._authority_batch_fixture(root, fixture)
            receipt_path = central / "thm_5_1" / "exact_mat_build_receipt_v1.json"
            payload = json.loads(receipt_path.read_text(encoding="utf-8"))
            payload["commit"] = "3" * 40
            receipt_path.write_text(json.dumps(payload), encoding="utf-8")
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                result = emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=Path(fixture["kenneth_repo"]),
                    expected_target_commit=str(context["commit"]), expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority, authority_manifest_sha256=sha256_file(authority),
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))

        with self.subTest(case="missing_consumer"), self._temporary_root() as root:
            fixture = self._fixture(root)
            authority, central, task_dir, context = self._authority_batch_fixture(root, fixture, consumers=["prob_5_1"])
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                result = emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=Path(fixture["kenneth_repo"]),
                    expected_target_commit=str(context["commit"]), expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority, authority_manifest_sha256=sha256_file(authority),
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))
            self.assertIn("consumer prob_5_1 exact-build receipt is missing", result["tasks"][0]["error"])

        with self.subTest(case="fake_absent"), self._temporary_root() as root:
            fixture = self._fixture(root)
            kenneth = Path(fixture["kenneth_repo"])
            matching = kenneth / "thm_5_1.lean"
            matching.write_text("theorem thm_5_1 : True := by trivial\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=kenneth, check=True)
            subprocess.run(["git", "commit", "-qm", "matching author file"], cwd=kenneth, check=True)
            fixture["kenneth_commit"] = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=kenneth, text=True).strip()
            authority, central, task_dir, context = self._authority_batch_fixture(root, fixture)
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                result = emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=kenneth,
                    expected_target_commit=str(context["commit"]), expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority, authority_manifest_sha256=sha256_file(authority),
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))
            self.assertIn("explicit author decision is required", result["tasks"][0]["error"])

    def test_batch_never_overwrites_partial_or_mismatched_existing_receipt(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            task_dir = self._batch_task(root, fixture)
            receipt_path = task_dir / "validated_boundary_delta_receipt_v1.json"
            partial = b'{"schema":"partial"'
            receipt_path.write_bytes(partial)
            result = self._emit_batch([task_dir], fixture)
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))
            self.assertEqual(receipt_path.read_bytes(), partial)

    def test_batch_missing_or_hash_mismatched_exact_build_fails_without_receipt(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            task_dir = self._batch_task(root, fixture)
            input_path = task_dir / "boundary_input_manifest.json"
            manifest = json.loads(input_path.read_text(encoding="utf-8"))
            manifest["planned_exact_build_receipts"]["target"]["sha256"] = "0" * 64
            input_path.write_text(json.dumps(manifest), encoding="utf-8")
            result = self._emit_batch([task_dir], fixture)
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))
            self.assertFalse((task_dir / "validated_boundary_delta_receipt_v1.json").exists())

    def test_batch_rejects_input_manifest_changed_during_build(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            task_dir = self._batch_task(root, fixture)
            input_path = task_dir / "boundary_input_manifest.json"
            original_build = boundary_module.build_verified_boundary_delta

            def changed_manifest(**kwargs):
                receipt = original_build(**kwargs)
                manifest = json.loads(input_path.read_text(encoding="utf-8"))
                manifest["concurrent_change"] = True
                input_path.write_text(json.dumps(manifest), encoding="utf-8")
                receipt["orchestration"]["input_manifest"] = {
                    "path": str(input_path.resolve()), "sha256": sha256_file(input_path),
                }
                return receipt

            with patch.object(boundary_module, "build_verified_boundary_delta", side_effect=changed_manifest):
                result = self._emit_batch([task_dir], fixture)
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))
            self.assertFalse((task_dir / "validated_boundary_delta_receipt_v1.json").exists())

    def test_malformed_existing_consumer_list_fails_one_task_without_stopping_batch(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            malformed_dir = self._batch_task(root / "malformed", fixture)
            next_dir = self._batch_task(root / "next", fixture)
            self.assertEqual(self._emit_batch([malformed_dir], fixture)["emitted"], 1)
            receipt_path = malformed_dir / "validated_boundary_delta_receipt_v1.json"
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["artifacts"]["consumer_builds"] = None
            receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            result = self._emit_batch([malformed_dir, next_dir], fixture)
            self.assertEqual((result["emitted"], result["failed"]), (1, 1))
            self.assertTrue((next_dir / "validated_boundary_delta_receipt_v1.json").is_file())

    def test_batch_atomic_publish_failure_leaves_no_final_or_temporary_file(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            task_dir = self._batch_task(root, fixture)
            with patch.object(boundary_module.os, "link", side_effect=OSError("fixture publish failure")):
                result = self._emit_batch([task_dir], fixture)
            self.assertEqual((result["emitted"], result["failed"]), (0, 1))
            self.assertFalse((task_dir / "validated_boundary_delta_receipt_v1.json").exists())
            self.assertEqual(list(task_dir.glob(".*.tmp")), [])

    def test_atomic_no_replace_publish_preserves_concurrent_creator(self):
        with self._temporary_root() as root:
            output = root / "receipt.json"

            def concurrent_creator(_temporary, final):
                Path(final).write_bytes(b"peer receipt\n")
                raise FileExistsError("peer won")

            with patch.object(boundary_module.os, "link", side_effect=concurrent_creator):
                with self.assertRaises(BoundaryDeltaReceiptError):
                    boundary_module._atomic_publish_no_replace(
                        output, b"our receipt\n", label="fixture",
                    )
            self.assertEqual(output.read_bytes(), b"peer receipt\n")
            self.assertEqual(list(root.glob(".*.tmp")), [])

    def test_atomic_no_replace_publish_write_failure_leaves_no_output_or_temp(self):
        with self._temporary_root() as root:
            output = root / "receipt.json"
            with patch.object(boundary_module.os, "fsync", side_effect=OSError("fixture write failure")):
                with self.assertRaises(BoundaryDeltaReceiptError):
                    boundary_module._atomic_publish_no_replace(
                        output, b"receipt\n", label="fixture",
                    )
            self.assertFalse(output.exists())
            self.assertEqual(list(root.glob(".*.tmp")), [])

    def test_atomic_publish_reports_success_when_only_post_link_cleanup_is_deferred(self):
        with self._temporary_root() as root:
            output = root / "receipt.json"
            with patch.object(Path, "unlink", side_effect=PermissionError("fixture cleanup denial")):
                result = boundary_module._atomic_publish_no_replace(
                    output, b"receipt\n", label="fixture",
                )
            self.assertEqual(output.read_bytes(), b"receipt\n")
            self.assertEqual(result["temporary_cleanup"], "deferred")
            temporary = list(root.glob(".*.tmp"))
            self.assertEqual(len(temporary), 1)
            self.assertTrue(temporary[0].samefile(output))
            with self.assertRaises(BoundaryDeltaReceiptError):
                boundary_module._atomic_publish_no_replace(
                    output, b"replacement\n", label="fixture retry",
                )
            self.assertEqual(output.read_bytes(), b"receipt\n")

    def test_original_authority_and_input_mutation_after_snapshot_does_not_change_replay_source(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            authority_path, central, task_dir, context = self._authority_batch_fixture(root, fixture)
            authority_sha = sha256_file(authority_path)
            input_path = task_dir / "boundary_input_manifest_reanchored_v1.json"
            input_sha = sha256_file(input_path)
            original_build = boundary_module.build_verified_boundary_delta

            def mutate_originals_after_prepare(**kwargs):
                authority = json.loads(authority_path.read_text(encoding="utf-8"))
                authority["concurrent_original_mutation"] = True
                authority_path.write_text(json.dumps(authority), encoding="utf-8")
                manifest = json.loads(input_path.read_text(encoding="utf-8"))
                manifest["concurrent_original_mutation"] = True
                input_path.write_text(json.dumps(manifest), encoding="utf-8")
                return original_build(**kwargs)

            with patch.object(boundary_module, "_exact_catalog_context", return_value=context), patch.object(
                boundary_module, "build_verified_boundary_delta", side_effect=mutate_originals_after_prepare,
            ):
                result = emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=Path(fixture["kenneth_repo"]),
                    expected_target_commit=json.loads(Path(fixture["target_build"]).read_text())["commit"],
                    expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority_path, authority_manifest_sha256=authority_sha,
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual((result["emitted"], result["failed"]), (1, 0), result)
            receipt_path = task_dir / "validated_boundary_delta_receipt_v1.json"
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(receipt["orchestration"]["batch_authority_original"]["sha256"], authority_sha)
            self.assertEqual(
                receipt["orchestration"]["batch_authority_input_original"]["resolved"]["sha256"],
                input_sha,
            )
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context):
                validate_verified_boundary_delta(
                    receipt_path, source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=Path(fixture["kenneth_repo"]),
                )

    def test_content_addressed_snapshot_collision_mismatch_is_never_overwritten(self):
        with self._temporary_root() as root:
            fixture = self._fixture(root)
            authority_path, central, task_dir, context = self._authority_batch_fixture(root, fixture)
            authority_sha = sha256_file(authority_path)
            collision = task_dir.parent / "_evidence" / "authority" / f"{authority_sha}.json"
            collision.parent.mkdir(parents=True)
            collision.write_text("{}", encoding="utf-8")
            with patch.object(boundary_module, "_exact_catalog_context", return_value=context), self.assertRaises(
                BoundaryDeltaReceiptError,
            ):
                emit_verified_boundary_delta_batch(
                    task_dirs=[task_dir], source_repos=[Path(fixture["source_repo"])],
                    target_repo=Path(fixture["target_repo"]), kenneth_repo=Path(fixture["kenneth_repo"]),
                    expected_target_commit=json.loads(Path(fixture["target_build"]).read_text())["commit"],
                    expected_kenneth_commit=str(fixture["kenneth_commit"]),
                    authority_manifest_path=authority_path, authority_manifest_sha256=authority_sha,
                    workspace_root=root, exact_build_root=central,
                )
            self.assertEqual(collision.read_text(encoding="utf-8"), "{}")
            self.assertFalse((task_dir / "validated_boundary_delta_receipt_v1.json").exists())

    def test_cli_rejects_absolute_and_parent_task_root_escape(self):
        with self._temporary_root() as root:
            command = [
                "python", "tools/mat_verified_boundary_delta.py", "emit-batch",
                "--task-root", str(root / "tasks"), "--source-repo", str(root),
                "--target-repo", str(root), "--kenneth-repo", str(root),
                "--target-commit", "a" * 40, "--kenneth-commit", "b" * 40,
            ]
            for task in (str((root / "outside" / "thm_5_1").resolve()), "../thm_5_1"):
                with self.subTest(task=task):
                    result = subprocess.run(
                        [*command, "--task", task], cwd=Path(__file__).resolve().parents[1],
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
                    )
                    self.assertEqual(result.returncode, 2)
                    self.assertIn("canonical task id", result.stderr)

    def test_nonempty_consumer_uses_current_catalog_subject_and_strict_receipt(self):
        with self._temporary_root() as root:
            commit = "c" * 40
            target = SubjectBundle.from_files(
                task_id="thm_5_1", files={"Probability/thm_5_1.lean": "theorem target : True := by trivial\n"},
                primary_path="Probability/thm_5_1.lean", source_repo="mat", source_commit=commit,
                layout="mat", subject_kind="catalog_git_bundle",
            )
            consumer = SubjectBundle.from_files(
                task_id="prob_5_1", files={"Probability/prob_5_1.lean": "theorem consumer : True := by trivial\n"},
                primary_path="Probability/prob_5_1.lean", source_repo="mat", source_commit=commit,
                layout="mat", subject_kind="catalog_git_bundle",
            )
            manifest = {
                "schema": "mat.catalog.direct-consumer-manifest.v1", "task_id": "thm_5_1",
                "commit": commit, "subject_id": target.subject_id, "bundle_hash": target.bundle_hash,
                "consumers": [{"task_id": "prob_5_1", "paths": [consumer.primary_path]}],
            }
            manifest_path = root / "consumers.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            module = "Probability.prob_5_1"
            build = {
                "schema": "mat.catalog.exact-build.v1", "campaign_id": "fixture",
                "task_id": consumer.task_id, "commit": commit, "subject_id": consumer.subject_id,
                "bundle_hash": consumer.bundle_hash, "primary_hash": consumer.primary_hash,
                "primary_path": consumer.primary_path, "subject_files": consumer.manifest(),
                "success": True, "exit_code": 0, "created_at": "2026-08-08T00:00:00+00:00",
                "focused_build": {
                    "command": ["lake", "build", module], "task_module": module,
                    "task_module_in_combined_command": True, "task_modules": [module],
                    "task_modules_in_combined_command": {module: True},
                    "batch_index": 1, "batch_size": 1, "cwd": str(root.resolve()),
                    "exit_code": 0, "duration_seconds": 1.0, "stdout": "", "stderr": "",
                },
                "forbidden_token_scan": {
                    "exit_code": 0, "findings": {}, "tokens": sorted(FORBIDDEN_PATTERNS),
                },
                "lean_tree_equivalence": {
                    "build_commit": commit, "target_commit": commit,
                    "changed_lean_files": [], "build_checkout_clean": True,
                },
            }
            build_path = root / "consumer_build.json"
            build_path.write_text(json.dumps(build), encoding="utf-8")
            catalog = SimpleNamespace(mat_commit=commit)
            with (
                patch.object(boundary_module, "load_catalog", return_value=catalog),
                patch.object(boundary_module, "discover_catalog_git_subjects", return_value={consumer.task_id: consumer}),
                patch.object(
                    boundary_module, "catalog_owned_build_modules",
                    return_value=({consumer.task_id: module}, {consumer.task_id: (module,)}),
                ),
            ):
                evidence = _consumer_evidence(
                    manifest_path, [build_path], task_id=target.task_id,
                    target=target, target_repo=root,
                )
                self.assertEqual(evidence[0]["task_id"], consumer.task_id)
                manifest["consumers"][0]["paths"] = ["Probability/not_owned.lean"]
                manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
                with self.assertRaises(BoundaryDeltaReceiptError):
                    _consumer_evidence(
                        manifest_path, [build_path], task_id=target.task_id,
                        target=target, target_repo=root,
                    )

    def test_author_exact_binds_real_kenneth_and_target_bytes(self):
        with self._temporary_root() as root:
            lean = "theorem thm_5_1_author : True := by trivial\n"
            kenneth, commit, _ = self._repo(root, "kenneth_exact", {"Probability/thm_5_1.lean": lean})
            decision = {
                "schema": "toy-apollo.boundary-delta-author-decision.v1",
                "task_id": "thm_5_1", "commit": commit,
                "decision": "author_exact", "matched_files": ["Probability/thm_5_1.lean"],
                "target_pairs": [{"kenneth_path": "Probability/thm_5_1.lean", "target_path": "Target/thm_5_1.lean"}],
            }
            decision_path = root / "decision.json"; decision_path.write_text(json.dumps(decision), encoding="utf-8")
            result = _author_provenance(
                task_id="thm_5_1", kenneth_repo=kenneth, kenneth_commit=commit,
                author_decision_path=decision_path,
                target_files={"Target/thm_5_1.lean": lean},
            )
            self.assertEqual(result["target_byte_bindings"][0]["content_sha256"], hashlib.sha256(lean.encode("utf-8")).hexdigest())
            with self.assertRaises(BoundaryDeltaReceiptError):
                _author_provenance(
                    task_id="thm_5_1", kenneth_repo=kenneth, kenneth_commit=commit,
                    author_decision_path=decision_path,
                    target_files={"Target/thm_5_1.lean": lean.replace("True", "False")},
                )

    def test_explicit_author_decision_requires_real_historical_evidence(self):
        with self._temporary_root() as root:
            kenneth, commit, _ = self._repo(root, "kenneth_decision", {"Probability/thm_5_1.lean": "theorem author : True := by trivial\n"})
            gate2 = root / "Gate2" / "review_apply_receipt.json"; gate2.parent.mkdir(); gate2.write_text("historical decision", encoding="utf-8")
            decision = {
                "schema": "toy-apollo.boundary-delta-author-decision.v1",
                "task_id": "thm_5_1", "commit": commit,
                "decision": "explicit_author_decision", "matched_files": ["Probability/thm_5_1.lean"],
                "authority_evidence": [{"kind": "gate2", "path": str(gate2), "sha256": sha256_file(gate2)}],
            }
            decision_path = root / "decision.json"; decision_path.write_text(json.dumps(decision), encoding="utf-8")
            result = _author_provenance(
                task_id="thm_5_1", kenneth_repo=kenneth, kenneth_commit=commit,
                author_decision_path=decision_path, target_files={"Target.lean": "different"},
            )
            self.assertEqual(result["authority_evidence"][0]["sha256"], sha256_file(gate2))
            decision["authority_evidence"][0]["sha256"] = "0" * 64
            decision_path.write_text(json.dumps(decision), encoding="utf-8")
            with self.assertRaises(BoundaryDeltaReceiptError):
                _author_provenance(
                    task_id="thm_5_1", kenneth_repo=kenneth, kenneth_commit=commit,
                    author_decision_path=decision_path, target_files={"Target.lean": "different"},
                )

    def test_rebuild_inventory_discovers_boundary_receipt_separately(self):
        with self._temporary_root() as root:
            receipt = root / "validated_boundary_delta_receipt_thm_5_1.json"
            receipt.write_text("{}", encoding="utf-8")
            inventory = discover_evidence_inventory([root])
            self.assertEqual(inventory.boundary_delta_receipts, (receipt.resolve(),))
            self.assertEqual(inventory.validated_transformation_receipts, ())

    def test_recovery_subject_exact_scope_is_registered_but_legacy_is_rejected(self):
        with self._temporary_root() as root:
            source_test = _recovery_test_module.HistoricalReviewApplyRecoveryTests()
            paths = source_test._write_pack(root)
            authority = build_historical_review_apply_recovery(
                pack_dir=paths["pack"], result_path=paths["result"], verify_path=paths["verify"],
                created_at="2026-08-08T00:00:00+00:00",
            )
            authority_path = root / "recovery.json"; authority_path.write_text(json.dumps(authority), encoding="utf-8")
            source = _source_scope(authority_path, task_id="thm_5_1", authority=authority)
            self.assertEqual(source.subject_kind, "review_input_bundle")
            legacy = json.loads(json.dumps(authority)); legacy["source_subject"]["subject_kind"] = "legacy_bound"
            legacy_path = root / "legacy_recovery.json"; legacy_path.write_text(json.dumps(legacy), encoding="utf-8")
            with self.assertRaises(BoundaryDeltaReceiptError):
                _source_scope(legacy_path, task_id="thm_5_1", authority=legacy)

    def test_real_def_5_2_embedded_source_scope_routes_only_registered_recovery_schema(self):
        workspace = Path(__file__).resolve().parents[2]
        manifest_path = (
            workspace / "toy-apollo-artifacts" / "validated_boundary_deltas"
            / "11a7948f" / "def_5_2" / "boundary_input_manifest_reanchored_v1.json"
        )
        if not manifest_path.is_file():
            self.skipTest("private boundary-97 evidence is not included in the public source snapshot")
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        authority_ref = manifest["source_authority"]
        authority_path = workspace / authority_ref["path"]
        self.assertEqual(sha256_file(authority_path), authority_ref["sha256"])
        resolved = _resolve_registered_source_scope(
            manifest["source_scope"], source_authority_path=authority_path,
            workspace_root=workspace, manifest_path=manifest_path, task_id="def_5_2",
        )
        self.assertEqual(resolved, authority_path.resolve())

        for key, replacement in (
            ("validator", "unknown.validator"),
            ("bundle_hash", "0" * 64),
        ):
            malformed = json.loads(json.dumps(manifest["source_scope"]))
            malformed[key] = replacement
            with self.subTest(key=key), self.assertRaises(BoundaryDeltaReceiptError):
                _resolve_registered_source_scope(
                    malformed, source_authority_path=authority_path,
                    workspace_root=workspace, manifest_path=manifest_path, task_id="def_5_2",
                )

    def test_real_boundary97_source_scope_routes_cover_all_four_registered_shapes(self):
        workspace = Path(__file__).resolve().parents[2]
        root = workspace / "toy-apollo-artifacts" / "validated_boundary_deltas" / "11a7948f"
        cases = {
            "def_5_2": "embedded_recovery_exact_bundle",
            "def_3_3": "workspace_review_binding",
            "def_10_1": "recovery_exact_bundle",
            "ex_11_5_2": "legacy_embedded_single_file",
        }
        if not all(
            (root / task_id / "boundary_input_manifest_reanchored_v1.json").is_file()
            for task_id in cases
        ):
            self.skipTest("private boundary-97 evidence is not included in the public source snapshot")
        for task_id, shape in cases.items():
            with self.subTest(task_id=task_id, shape=shape):
                manifest_path = root / task_id / "boundary_input_manifest_reanchored_v1.json"
                manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                authority_path = Path(manifest["source_authority"]["path"])
                authority_path = authority_path if authority_path.is_absolute() else workspace / authority_path
                resolved = _resolve_registered_source_scope(
                    manifest["source_scope"], source_authority_path=authority_path,
                    workspace_root=workspace, manifest_path=manifest_path, task_id=task_id,
                )
                self.assertTrue(resolved.is_file())
                malformed = json.loads(json.dumps(manifest["source_scope"]))
                malformed["unknown_structure"] = True
                with self.assertRaises(BoundaryDeltaReceiptError):
                    _resolve_registered_source_scope(
                        malformed, source_authority_path=authority_path,
                        workspace_root=workspace, manifest_path=manifest_path, task_id=task_id,
                    )

    def test_importer_uses_recovered_review_directly_without_creating_review(self):
        with self._temporary_root() as root:
            commit = "b" * 40
            plan = json.dumps([{"block_id": "thm_5_1", "type": "Theorem_with_Proof", "title": "Fixture", "content": "claim", "dependencies": [], "source_plan": "fixture"}]).encode()
            manifest = (
                "group,chapter,file_path,basename,module_name,ledger_task_match,ledger_status,phase2_status,classification,axiom_count,sorry_or_admit_in_code\n"
                "ProbabilityTheory/chapter_05,5,ProbabilityTheory/chapter_05/thm_5_1.lean,thm_5_1,ProbabilityTheory.chapter_05.thm_5_1,yes,COMPLETED,pass,ledger_task_module,0,no\n"
            ).encode()
            catalog = build_catalog(
                catalog_name="fixture", toy_commit="a" * 40, mat_commit=commit,
                plan_documents={"plan.json": plan}, manifest_bytes=manifest,
                family_overrides=[], restored_task_ids=[], legacy_cohort_id="legacy",
                mat_tree_paths=["ProbabilityTheory/chapter_05/thm_5_1.lean"],
            )
            source = SubjectBundle.from_files(
                task_id="thm_5_1", files={"review/thm_5_1.lean": "theorem fixture : True := by trivial\n"},
                primary_path="review/thm_5_1.lean", source_repo="toy_apollo",
                layout="historical_review", subject_kind="review_input_bundle",
            )
            target = SubjectBundle.from_files(
                task_id="thm_5_1", files={"ProbabilityTheory/chapter_05/thm_5_1.lean": "theorem fixture : True := by trivial\n"},
                primary_path="ProbabilityTheory/chapter_05/thm_5_1.lean", source_repo="mat",
                source_commit=commit, layout="mat", subject_kind="catalog_git_bundle",
            )
            store = WorkspaceStateStore(root / "state.sqlite3"); store.persist_catalog(catalog)
            store.upsert_subject(source); store.upsert_subject(target)
            result_hash = "c" * 64
            review_id = store.record_review(
                task_id="thm_5_1", subject_id=source.subject_id, verdict="pass",
                proof_class="fixture", completion_class="fixture",
                phase2_status="pass", evidence_path=root / "result.json",
                evidence_hash=result_hash,
                authority_scope="recovered_historical_phase2_review_apply",
                authority_eligible=True, prompt_version=11, rubric_version=9,
            )
            store.set_task_head(task_id="thm_5_1", role="mat_main", subject_id=target.subject_id)
            receipt = {
                "schema": BOUNDARY_DELTA_SCHEMA, "task_id": "thm_5_1",
                "created_at": "2026-08-08T00:00:00+00:00",
                "transformation_kind": "verified_boundary_delta", "semantic_upgrade": False,
                "source_authority": {"review_id": review_id, "prompt_version": 11, "rubric_version": 9, "result_evidence_hash": result_hash},
                "artifacts": {"source_scope": {"schema": "toy-apollo.historical-review-apply-recovery.v1", "sha256": "d" * 64}},
                "checks": {key: "pass" for key in (
                    "source_applied_modern_r9_pass", "source_complete_bundle",
                    "target_complete_bundle_at_pinned_commit", "per_file_diff_classified",
                    "lean_payload_token_invariant", "public_declaration_signatures_unchanged",
                    "import_boundary_exactly_declared", "target_build_and_forbidden_scan",
                    "direct_consumers_built_and_scanned", "kenneth_provenance_or_author_decision",
                    "no_semantic_or_rubric_upgrade",
                )},
            }
            receipt_path = root / "validated_boundary_delta_receipt_thm_5_1.json"; receipt_path.write_text(json.dumps(receipt), encoding="utf-8")
            report = MigrationReport(database=str(store.path))
            with patch("src.toy_apollo.state_migration.validate_verified_boundary_delta", return_value=(receipt, source, target)):
                import_verified_boundary_delta_receipt(
                    store, receipt_path, report,
                    source_repos=[root], target_repo=root, kenneth_repo=root,
                )
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT count(*) FROM reviews").fetchone()[0], 1)
                row = connection.execute("SELECT transformation_kind FROM transformations").fetchone()
            self.assertEqual(row["transformation_kind"], "verified_boundary_delta")

    def test_content_resolver_canonicalizes_crlf_and_searches_multiple_roots(self):
        with self._temporary_root() as root:
            logical = "review/thm_5_1.lean"
            lean = "theorem fixture : True := by trivial\n"
            subject = SubjectBundle.from_files(
                task_id="thm_5_1", files={logical: lean}, primary_path=logical,
                source_repo="toy_apollo", subject_kind="review_input_bundle",
            )
            missing = root / "missing"; missing.mkdir()
            artifact = root / "snapshot" / logical; artifact.parent.mkdir(parents=True)
            artifact.write_bytes(lean.replace("\n", "\r\n").encode())
            content, provenance = _bundle_content([missing, root / "snapshot"], subject, label="source")
            self.assertEqual(content[logical], lean)
            self.assertEqual(provenance[0]["kind"], "artifact_file")
            artifact.write_text(lean.replace("True", "False"), encoding="utf-8")
            with self.assertRaises(BoundaryDeltaReceiptError):
                _bundle_content([missing, root / "snapshot"], subject, label="source")

    def test_kenneth_task_matching_rejects_numeric_prefix_collision(self):
        with self._temporary_root() as root:
            kenneth, commit, _ = self._repo(root, "kenneth_collision", {
                "Probability/thm_5_10.lean": "theorem other : True := by trivial\n",
                "Probability/thm_5_1_support.lean": "theorem support : True := by trivial\n",
            })
            decision = {
                "schema": "toy-apollo.boundary-delta-author-decision.v1", "task_id": "thm_5_1",
                "commit": commit, "decision": "author_exact",
                "matched_files": ["Probability/thm_5_1_support.lean"],
                "target_pairs": [{"kenneth_path": "Probability/thm_5_1_support.lean", "target_path": "Target/thm_5_1_support.lean"}],
            }
            path = root / "decision.json"; path.write_text(json.dumps(decision), encoding="utf-8")
            result = _author_provenance(
                task_id="thm_5_1", kenneth_repo=kenneth, kenneth_commit=commit,
                author_decision_path=path,
                target_files={"Target/thm_5_1_support.lean": "theorem support : True := by trivial\n"},
            )
            self.assertEqual(result["matched_files"], ["Probability/thm_5_1_support.lean"])

    def test_legacy_embedded_single_file_scope_passes_and_rejects_hash_or_multifile(self):
        with self._temporary_root() as root:
            lean = "theorem legacy_fixture : True := by trivial\n"
            digest = hashlib.sha256(lean.encode()).hexdigest()
            reviewed = SubjectBundle.from_legacy_hash(
                task_id="thm_5_1", candidate_hash=digest, evidence_hash="e" * 64,
                source_repo="toy_apollo",
            )
            input_payload = {"review_subject_hash": digest, "candidate": {"hash": digest, "lean": lean}}
            input_path = root / "semantic_review_input_v1.json"; input_path.write_text(json.dumps(input_payload), encoding="utf-8")
            authority = {
                "schema": "toy-apollo.historical-review-apply-recovery.v1",
                "artifacts": {"input": {"path": input_path.name, "sha256": sha256_file(input_path)}},
            }
            receipt_path = root / "recovery.json"; receipt_path.write_text(json.dumps(authority), encoding="utf-8")
            source, content, provenance = _legacy_embedded_single_file_scope(
                receipt_path, authority, task_id="thm_5_1", authority=authority,
                reviewed_subject=reviewed,
            )
            self.assertEqual(content[source.primary_path], lean)
            self.assertEqual(provenance[0]["kind"], "validated_recovery_embedded_candidate")
            bad = json.loads(json.dumps(input_payload)); bad["candidate"]["hash"] = "0" * 64
            input_path.write_text(json.dumps(bad), encoding="utf-8")
            authority["artifacts"]["input"]["sha256"] = sha256_file(input_path)
            receipt_path.write_text(json.dumps(authority), encoding="utf-8")
            with self.assertRaises(BoundaryDeltaReceiptError):
                _legacy_embedded_single_file_scope(receipt_path, authority, task_id="thm_5_1", authority=authority, reviewed_subject=reviewed)
            multi = SubjectBundle.from_manifest(
                task_id="thm_5_1", files=[*reviewed.manifest(), {"path": "legacy/support.lean", "content_sha256": digest, "git_blob_sha": "", "size": 0}],
                primary_path=reviewed.primary_path, source_repo="toy_apollo", subject_kind="legacy_bound",
            )
            with self.assertRaises(BoundaryDeltaReceiptError):
                _legacy_embedded_single_file_scope(receipt_path, authority, task_id="thm_5_1", authority=authority, reviewed_subject=multi)

    def test_declared_import_open_and_section_boundary_changes_are_exact(self):
        source_path = "Toy/fixture.lean"; target_path = "Probability/fixture.lean"
        source = {source_path: "import Toy.Base\nopen Set ProbabilityTheory\ntheorem fixture : True := by trivial\n"}
        target = {target_path: "import Probability.Base\nimport Mathlib\nsection Fixture\nopen Set\ntheorem fixture : True := by trivial\nend Fixture\n"}
        policy = {
            "file_pairs": [{"source": source_path, "target": target_path}],
            "module_rewrites": [{"source": "Toy.Base", "target": "Probability.Base"}],
            "import_changes": [{
                "source_path": source_path, "target_path": target_path,
                "source_imports": ["Toy.Base"],
                "normalized_source_imports": ["Probability.Base"],
                "target_imports": ["Probability.Base", "Mathlib"],
            }],
            "open_namespace_changes": [{
                "source_path": source_path, "target_path": target_path,
                "source_open": ["Set", "ProbabilityTheory"], "target_open": ["Set"],
            }],
            "section_changes": [{
                "source_path": source_path, "target_path": target_path,
                "source_sections": [], "target_sections": ["section Fixture", "end Fixture"],
            }],
        }
        rows, _, _, declarations = _compare_files(
            source, target, policy, {"Toy.Base": "Probability.Base"}, task_id="thm_5_1",
        )
        self.assertEqual(len(rows), 1); self.assertEqual(len(declarations), 1)
        del policy["section_changes"]
        with self.assertRaises(BoundaryDeltaReceiptError):
            _compare_files(source, target, policy, {"Toy.Base": "Probability.Base"}, task_id="thm_5_1")


if __name__ == "__main__":
    unittest.main()
