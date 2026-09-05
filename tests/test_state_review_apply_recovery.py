from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from formalization_engine.phase2_semantic_review import render_semantic_review_prompt
from formalization_engine.state_bundle_delta import analyze_current_mat_bundles
from formalization_engine.state_migration import (
    MigrationReport,
    import_historical_review_apply_recovery_receipt,
    import_validated_transformation_receipt,
    rebuild_workspace_database,
)
from formalization_engine.state_review_apply_recovery import (
    HistoricalReviewApplyRecoveryError,
    build_historical_review_apply_recovery,
)
from formalization_engine.state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
)


def _hash_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


class HistoricalReviewApplyRecoveryTests(unittest.TestCase):
    task_id = "thm_5_1"
    mat_commit = "b" * 40

    def _write_pack(self, root: Path, *, prompt_version: int = 11) -> dict[str, Path]:
        pack = root / self.task_id
        pack.mkdir()
        lean = "theorem recovered_fixture : True := by trivial\n"
        candidate_hash = _hash_text(lean)
        subject_path = f"review/{self.task_id}.lean"
        manifest = [
            {
                "path": subject_path,
                "content_sha256": candidate_hash,
                "git_blob_sha": "a" * 40,
                "size": len(lean.encode("utf-8")),
            }
        ]
        task = {
            "block_id": self.task_id,
            "type": "Theorem_with_Proof",
            "title": "Fixture",
            "content": "The fixture claim.",
            "dependencies": [],
            "soft_imports": [],
        }
        required_evidence = [
            "source_tex",
            "lean_subject",
            "audit",
            "classification",
            "dependency_status",
            "downstream",
            "ledger_status",
            "hashes",
        ]
        basis = {"task": task, "required_evidence_classes": required_evidence}
        context = "# Exact review context\n"
        review_input = {
            "schema_version": "phase2.semantic_review.input.v3",
            "mode": "review-existing",
            "attempt": 1,
            "generated_at": "2026-07-20T00:00:00Z",
            "prompt_version": prompt_version,
            "rubric_version": 9,
            "task": task,
            "review_subject_kind": "official_output",
            "review_subject_file": subject_path,
            "review_subject_hash": candidate_hash,
            "subject_bundle": {
                "task_id": self.task_id,
                "primary_path": subject_path,
                "primary_hash": candidate_hash,
                "bundle_hash": sha256_json(manifest),
                "files": manifest,
                "source_repo": "formalization_engine",
                "source_commit": "",
                "layout": "historical_review",
                "subject_kind": "review_input_bundle",
            },
            "candidate": {"file": subject_path, "hash": candidate_hash, "lean": lean},
            "review_basis": basis,
            "review_basis_hash": sha256_json(basis),
            "review_context_markdown": context,
            "review_context_hash": _hash_text(context),
        }
        input_hash = sha256_json(review_input)
        input_path = pack / "semantic_review_input_v1.json"
        prompt_path = pack / "semantic_review_prompt_v1.md"
        context_path = pack / "semantic_review_context_v1.md"
        request_path = pack / "semantic_review_request_v1.json"
        result_path = pack / "semantic_review_result_v1.json"
        verify_path = pack / "verify_result_v2.json"
        input_path.write_text(json.dumps(review_input, indent=2), encoding="utf-8")
        prompt_path.write_text(render_semantic_review_prompt(review_input), encoding="utf-8")
        context_path.write_text(context, encoding="utf-8")
        request = {
            "schema_version": "phase2.semantic_review.request.v1",
            "task_id": self.task_id,
            "attempt": 1,
            "review_input_hash": input_hash,
            "review_subject_hash": candidate_hash,
            "review_basis_hash": review_input["review_basis_hash"],
            "review_input_file": input_path.name,
            "review_prompt_file": prompt_path.name,
            "review_context_file": context_path.name,
            "expected_result_file": result_path.name,
            "prompt_version": prompt_version,
            "rubric_version": 9,
        }
        request_path.write_text(json.dumps(request, indent=2), encoding="utf-8")
        independence = {
            "role": "independent_read_only_reviewer",
            "read_only": True,
            "did_edit_candidate": False,
            "used_current_review_request": True,
            "attestation": "Independent fixture review.",
        }
        result = {
            "schema_version": "phase2.semantic_review.result.v8",
            "task_id": self.task_id,
            "attempt": 1,
            "prompt_version": prompt_version,
            "rubric_version": 9,
            "review_input_hash": input_hash,
            "review_input_file": input_path.name,
            "review_prompt_file": prompt_path.name,
            "review_context_file": context_path.name,
            "candidate_hash": candidate_hash,
            "verdict": "pass",
            "confidence": "high",
            "summary": "Independent exact-source fixture review.",
            "proof_class": "textbook_proof_completed",
            "completion_class": "source_faithful_proof_completed",
            "phase2_status": "pass",
            "reviewer_independence": independence,
            "reviewer_backend_id": "codex-handoff",
            "source_claims": [{"claim": "The fixture claim.", "status": "covered"}],
            "claim_mapping": [
                {"source_claim": "The fixture claim.", "lean_declaration": "recovered_fixture"}
            ],
            "route_inspection": {
                "status": "covered",
                "source_route": "Direct proof.",
                "expected_answer_or_statement": "True.",
                "local_mathlib_search": "No search needed.",
                "public_interface_check": "No relocated premise.",
                "support_or_reassembly_decision": "No support needed.",
                "stop_go_verdict": "go",
                "notes": "Exact fixture route.",
            },
            "spine_alignment": (
                {
                    "status": "covered",
                    "summary": "Direct source step.",
                    "obligations_checked": [
                        {
                            "source_obligation": "The fixture claim.",
                            "lean_landing": "recovered_fixture",
                            "status": "covered",
                        }
                    ],
                    "missing_obligations": [],
                    "shortcut_assessment": "faithful_abstraction",
                }
                if prompt_version <= 10
                else {
                    "status": "covered",
                    "summary": "Direct source step.",
                    "source_steps_checked": [
                        {
                            "source_step": "The fixture claim.",
                            "lean_landing": "recovered_fixture",
                            "landing_kind": "theorem",
                            "signature_match": "passed",
                            "body_reassumption_check": "passed",
                            "public_premise_check": "passed",
                            "notes": "Direct fixture proof.",
                        }
                    ],
                    "missing_source_steps": [],
                    "shortcut_assessment": "faithful_abstraction",
                }
            ),
            "evidence_review": {
                "status": "covered",
                "summary": "All bound fixture evidence checked.",
                "items": [
                    {
                        "evidence_class": item,
                        "status": "covered",
                        "evidence": f"checked {item}",
                    }
                    for item in required_evidence
                ],
                "blocking_issues": [],
            },
            "interface_contract": {
                "status": "covered",
                "summary": "Exact interface.",
                "mismatches": [],
            },
            "downstream_adequacy": {
                "status": "covered",
                "summary": "No consumers.",
                "consumers_checked": [],
                "blocking_issues": [],
            },
            "forbidden_weakenings": [
                {"status": "not_present", "summary": "No weakening."}
            ],
            "findings": [],
            "recommended_disposition": "promote",
            "runner": {
                "status": "codex_handoff_applied",
                "result_file": result_path.name,
            },
        }
        if prompt_version <= 10:
            result["obligation_review"] = {
                "status": "covered",
                "summary": "Legacy obligation schema covered.",
                "items": [],
                "open_blockers": [],
                "scaffold_assessment": [],
            }
        result_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
        verify = {
            "task_id": self.task_id,
            "attempt": 2,
            "candidate_hash": candidate_hash,
            "verified_at": "2026-07-20T00:05:00Z",
            "success": True,
            "mode": "review-apply",
            "disposition": "official_output_review_pass",
            "state_transition": "none",
            "final_build": {"success": True, "output": "built"},
            "diagnostics": [],
            "semantic_review": {
                "verdict": "pass",
                "proof_class": result["proof_class"],
                "completion_class": result["completion_class"],
                "phase2_status": "pass",
                "runner_status": "codex_handoff_applied",
                "review_result_file": result_path.name,
                "review_input_file": input_path.name,
                "review_prompt_file": prompt_path.name,
            },
        }
        verify_path.write_text(json.dumps(verify, indent=2), encoding="utf-8")
        (pack / "metadata.json").write_text(
            json.dumps({"task_id": self.task_id, "phase2_status": "pass"}, indent=2),
            encoding="utf-8",
        )
        return {
            "pack": pack,
            "result": result_path,
            "verify": verify_path,
            "input": input_path,
            "request": request_path,
        }

    def _emit_receipt(self, paths: dict[str, Path]) -> tuple[Path, dict]:
        receipt = build_historical_review_apply_recovery(
            pack_dir=paths["pack"],
            result_path=paths["result"],
            verify_path=paths["verify"],
            created_at="2026-08-08T00:00:00+00:00",
        )
        path = paths["pack"] / "historical_review_apply_recovery_receipt_v1.json"
        path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        return path, receipt

    def test_valid_p10_and_p11_recover_source_authority_idempotently(self):
        for prompt_version in (10, 11):
            with self.subTest(prompt_version=prompt_version), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                paths = self._write_pack(root, prompt_version=prompt_version)
                receipt_path, receipt = self._emit_receipt(paths)
                store = WorkspaceStateStore(root / "state.sqlite3")
                report = MigrationReport(database=str(store.path))

                import_historical_review_apply_recovery_receipt(store, receipt_path, report)
                import_historical_review_apply_recovery_receipt(store, receipt_path, report)

                self.assertEqual(report.historical_apply_recovery_receipts, 1)
                self.assertEqual(report.skipped, 1)
                with store._connection(write=False) as connection:
                    row = connection.execute(
                        "SELECT authority_scope, authority_eligible, subject_id FROM reviews"
                    ).fetchone()
                self.assertEqual(row["authority_scope"], "recovered_historical_phase2_review_apply")
                self.assertEqual(row["authority_eligible"], 1)
                self.assertEqual(row["subject_id"], receipt["source_subject"]["subject_id"])

    def test_missing_serialized_phase2_status_uses_canonical_review_apply_projection(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = self._write_pack(Path(tmp), prompt_version=9)
            result = json.loads(paths["result"].read_text(encoding="utf-8"))
            result.pop("phase2_status")
            review_input = json.loads(paths["input"].read_text(encoding="utf-8"))
            review_input.pop("subject_bundle")
            paths["input"].write_text(json.dumps(review_input, indent=2), encoding="utf-8")
            (paths["pack"] / "semantic_review_prompt_v1.md").write_text(
                render_semantic_review_prompt(review_input),
                encoding="utf-8",
            )
            result["review_input_hash"] = sha256_json(review_input)
            paths["result"].write_text(json.dumps(result, indent=2), encoding="utf-8")
            request = json.loads(paths["request"].read_text(encoding="utf-8"))
            request.pop("review_input_hash")
            paths["request"].write_text(json.dumps(request, indent=2), encoding="utf-8")

            receipt = build_historical_review_apply_recovery(
                pack_dir=paths["pack"],
                result_path=paths["result"],
                verify_path=paths["verify"],
            )

            self.assertEqual(receipt["source_review"]["phase2_status"], "pass")
            self.assertEqual(
                receipt["checks"]["phase2_projection_source"],
                "canonical_review_decision_plus_versioned_review_apply",
            )
            self.assertEqual(
                receipt["checks"]["request_input_binding_source"],
                "versioned_result_hash_plus_request_subject_basis_paths",
            )

            verify = json.loads(paths["verify"].read_text(encoding="utf-8"))
            verify["semantic_review"]["phase2_status"] = "fail"
            paths["verify"].write_text(json.dumps(verify, indent=2), encoding="utf-8")
            with self.assertRaises(HistoricalReviewApplyRecoveryError):
                build_historical_review_apply_recovery(
                    pack_dir=paths["pack"],
                    result_path=paths["result"],
                    verify_path=paths["verify"],
                )

    def test_recovery_validation_fails_closed(self):
        cases = (
            "rubric8",
            "tampered_input",
            "failed_projection",
            "missing_verify",
            "failed_build",
            "invalidated",
            "dependency_drift",
            "sidecar",
        )
        for case in cases:
            with self.subTest(case=case), tempfile.TemporaryDirectory() as tmp:
                paths = self._write_pack(Path(tmp))
                if case == "rubric8":
                    for key in ("result", "input", "request"):
                        payload = json.loads(paths[key].read_text(encoding="utf-8"))
                        payload["rubric_version"] = 8
                        paths[key].write_text(json.dumps(payload, indent=2), encoding="utf-8")
                elif case == "tampered_input":
                    payload = json.loads(paths["input"].read_text(encoding="utf-8"))
                    payload["task"]["title"] = "tampered"
                    paths["input"].write_text(json.dumps(payload, indent=2), encoding="utf-8")
                elif case == "failed_projection":
                    payload = json.loads(paths["result"].read_text(encoding="utf-8"))
                    payload["phase2_status"] = "fail"
                    paths["result"].write_text(json.dumps(payload, indent=2), encoding="utf-8")
                elif case == "missing_verify":
                    paths["verify"].unlink()
                elif case == "failed_build":
                    payload = json.loads(paths["verify"].read_text(encoding="utf-8"))
                    payload["final_build"]["success"] = False
                    paths["verify"].write_text(json.dumps(payload, indent=2), encoding="utf-8")
                elif case == "invalidated":
                    payload = json.loads(paths["result"].read_text(encoding="utf-8"))
                    payload["invalidated_by"] = "thm_5_2"
                    paths["result"].write_text(json.dumps(payload, indent=2), encoding="utf-8")
                elif case == "dependency_drift":
                    payload = json.loads((paths["pack"] / "metadata.json").read_text(encoding="utf-8"))
                    payload["dependency_reconciliation_requires_fresh_review"] = True
                    (paths["pack"] / "metadata.json").write_text(
                        json.dumps(payload, indent=2), encoding="utf-8"
                    )
                elif case == "sidecar":
                    payload = json.loads(paths["result"].read_text(encoding="utf-8"))
                    payload["reviewer_backend_id"] = "legacy-sidecar"
                    paths["result"].write_text(json.dumps(payload, indent=2), encoding="utf-8")

                with self.assertRaises(HistoricalReviewApplyRecoveryError):
                    build_historical_review_apply_recovery(
                        pack_dir=paths["pack"],
                        result_path=paths["result"],
                        verify_path=paths["verify"],
                    )

    def test_clean_rebuild_records_rejected_recovery_receipt_reason(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            evidence = root / "evidence"
            evidence.mkdir()
            paths = self._write_pack(evidence)
            receipt_path, receipt = self._emit_receipt(paths)
            rejected_path = paths["pack"] / "historical_review_apply_recovery_receipt_tampered.json"
            rejected = json.loads(json.dumps(receipt))
            rejected["source_review"]["prompt_version"] = 8
            rejected_path.write_text(json.dumps(rejected, indent=2), encoding="utf-8")
            state_path = root / "state.sqlite3"

            with patch(
                "formalization_engine.state_migration.refresh_workspace_state",
                return_value={
                    "local": {"mat_main": 0, "mat_candidate": 0, "toy_current": 0, "errors": []},
                    "remote": {"subjects": 0, "errors": []},
                },
            ):
                report = rebuild_workspace_database(
                    state_path=state_path,
                    workspace_root=root,
                    runtime_root=root,
                    roots=[evidence],
                    refresh_remote=False,
                )

            self.assertEqual(report.historical_apply_recovery_receipts, 1)
            self.assertEqual(report.rejected_historical_apply_recovery_receipts, 1)
            store = WorkspaceStateStore(state_path)
            with store._connection(write=False) as connection:
                row = connection.execute(
                    "SELECT payload_json FROM state_events "
                    "WHERE event_type = 'historical_review_apply_recovery_receipt_rejected'"
                ).fetchone()
            self.assertIsNotNone(row)
            self.assertIn("does not match validated evidence", json.loads(row[0])["validation_error"])

    def test_receipt_tamper_is_rejected_without_authority(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._write_pack(root)
            receipt_path, _ = self._emit_receipt(paths)
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["source_subject"]["bundle_hash"] = "0" * 64
            receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.initialize()

            with self.assertRaises(HistoricalReviewApplyRecoveryError):
                import_historical_review_apply_recovery_receipt(
                    store, receipt_path, MigrationReport(database=str(store.path))
                )
            with store._connection(write=False) as connection:
                self.assertEqual(connection.execute("SELECT COUNT(*) FROM reviews").fetchone()[0], 0)

    def test_existing_generic_identity_requires_clean_rebuild_without_promotion(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = self._write_pack(root)
            receipt_path, receipt = self._emit_receipt(paths)
            raw = receipt["source_subject"]
            subject = SubjectBundle.from_manifest(
                task_id=self.task_id,
                files=raw["files"],
                primary_path=raw["primary_path"],
                source_repo=raw["source_repo"],
                source_commit=raw["source_commit"],
                layout=raw["layout"],
                subject_kind=raw["subject_kind"],
            )
            store = WorkspaceStateStore(root / "state.sqlite3")
            store.upsert_subject(subject)
            store.record_review(
                task_id=self.task_id,
                subject_id=subject.subject_id,
                verdict="pass",
                proof_class=receipt["source_review"]["proof_class"],
                completion_class=receipt["source_review"]["completion_class"],
                phase2_status="pass",
                evidence_path=paths["result"],
                evidence_hash=receipt["artifacts"]["result"]["sha256"],
                authority_scope="phase2_review_artifact",
                authority_eligible=False,
                prompt_version=11,
                rubric_version=9,
            )

            with self.assertRaisesRegex(ValueError, "clean canonical rebuild"):
                import_historical_review_apply_recovery_receipt(
                    store, receipt_path, MigrationReport(database=str(store.path))
                )
            with store._connection(write=False) as connection:
                row = connection.execute(
                    "SELECT authority_eligible, authority_scope FROM reviews"
                ).fetchone()
            self.assertEqual(row["authority_eligible"], 0)
            self.assertEqual(row["authority_scope"], "phase2_review_artifact")

    def _write_transformation(
        self,
        root: Path,
        receipt: dict,
        target: SubjectBundle,
    ) -> Path:
        source = receipt["source_subject"]
        build = {
            "schema": "toy-apollo.mechanical-build-evidence.v1",
            "task_id": self.task_id,
            "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash,
            "primary_hash": target.primary_hash,
            "commit": target.source_commit,
            "status": "pass",
            "success": True,
            "exit_code": 0,
        }
        forbidden = {
            "schema": "toy-apollo.forbidden-scan-evidence.v1",
            "task_id": self.task_id,
            "subject_id": target.subject_id,
            "bundle_hash": target.bundle_hash,
            "primary_hash": target.primary_hash,
            "commit": target.source_commit,
            "status": "pass",
            "matches": [],
        }
        build_path = root / "build_evidence.json"
        scan_path = root / "forbidden_evidence.json"
        build_path.write_text(json.dumps(build), encoding="utf-8")
        scan_path.write_text(json.dumps(forbidden), encoding="utf-8")
        payload = {
            "schema": "toy-apollo.validated-transformation-receipt.v1",
            "task_id": self.task_id,
            "created_at": "2026-08-08T00:10:00+00:00",
            "transformation_kind": "path_relocation",
            "mechanical_status": "pass",
            "source_review": {
                "review_id": receipt["source_review"]["review_id"],
                "evidence_hash": receipt["artifacts"]["result"]["sha256"],
                "prompt_version": receipt["source_review"]["prompt_version"],
                "rubric_version": 9,
            },
            "source_subject": source,
            "target_subject": {
                "task_id": target.task_id,
                "subject_id": target.subject_id,
                "subject_kind": target.subject_kind,
                "source_repo": target.source_repo,
                "source_commit": target.source_commit,
                "layout": target.layout,
                "bundle_hash": target.bundle_hash,
                "primary_hash": target.primary_hash,
                "primary_path": target.primary_path,
                "files": target.manifest(),
            },
            "comparison": {
                "classification": "path_only_relocation",
                "primary_equal": True,
                "content_multiset_equal": True,
            },
            "checks": {
                "build": {
                    "status": "pass",
                    "artifact": {"path": build_path.name, "sha256": sha256_file(build_path)},
                },
                "forbidden_scan": {
                    "status": "pass",
                    "artifact": {"path": scan_path.name, "sha256": sha256_file(scan_path)},
                },
            },
        }
        path = root / "validated_transformation_receipt_thm_5_1.json"
        path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
        return path

    def test_clean_rebuild_recovers_source_then_applies_separate_transformation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            evidence = root / "evidence"
            evidence.mkdir()
            paths = self._write_pack(evidence)
            _, recovery = self._emit_receipt(paths)
            source_manifest = recovery["source_subject"]["files"]
            target_manifest = [dict(source_manifest[0])]
            target_manifest[0]["path"] = "ProbabilityTheory/chapter_05/thm_5_1.lean"
            target = SubjectBundle.from_manifest(
                task_id=self.task_id,
                files=target_manifest,
                primary_path=target_manifest[0]["path"],
                source_repo="mat",
                source_commit=self.mat_commit,
                layout="mat_main",
                subject_kind="mat_main",
            )
            self._write_transformation(paths["pack"], recovery, target)
            state_path = root / "state.sqlite3"
            def refresh(store, **_kwargs):
                store.initialize()
                with store._connection(write=True) as connection:
                    connection.execute(
                        """
                        INSERT OR REPLACE INTO catalog_versions(
                            catalog_id, schema_version, catalog_name, toy_commit, mat_commit,
                            manifest_sha256, plan_set_sha256, policy_sha256, counts_json,
                            payload_json, imported_at
                        ) VALUES ('catalog-test', 'test', 'test', ?, ?, ?, ?, ?, '{}', '{}', ?)
                        """,
                        (
                            "a" * 40,
                            self.mat_commit,
                            "1" * 64,
                            "2" * 64,
                            "3" * 64,
                            "2026-08-08T00:00:00+00:00",
                        ),
                    )
                    connection.execute(
                        "INSERT OR REPLACE INTO meta(key, value) VALUES('active_catalog_id', 'catalog-test')"
                    )
                store.upsert_subject(target)
                store.set_task_head(
                    task_id=self.task_id,
                    role="mat_main",
                    subject_id=target.subject_id,
                    freshness="fresh",
                )
                return {
                    "local": {"mat_main": 1, "mat_candidate": 0, "toy_current": 0, "errors": []},
                    "remote": {"subjects": 0, "errors": []},
                }

            with patch("formalization_engine.state_migration.refresh_workspace_state", side_effect=refresh):
                report = rebuild_workspace_database(
                    state_path=state_path,
                    workspace_root=root,
                    runtime_root=root,
                    roots=[evidence],
                    refresh_remote=False,
                )

            self.assertEqual(report.historical_apply_recovery_receipts, 1)
            self.assertEqual(report.validated_transformation_receipts, 1, report.warnings)
            rebuilt = WorkspaceStateStore(state_path)
            self.assertEqual(
                analyze_current_mat_bundles(rebuilt)["tasks"][0]["status"],
                "validated_rebind",
            )


if __name__ == "__main__":
    unittest.main()
