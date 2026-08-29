from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from src.toy_apollo.core.settings import Settings
from src.toy_apollo.state_migration import rebuild_workspace_database
from src.toy_apollo.state_pr_review import (
    ExternalPrReviewError,
    PullRequestObservation,
    adopt_external_pr_evidence,
    apply_external_pr_review,
    prepare_external_pr_review,
)
from src.toy_apollo.state_store import SubjectBundle, WorkspaceStateStore


class ExternalPrReviewTests(unittest.TestCase):
    task_id = "thm_1_1"
    code = "import Mathlib\n\ntheorem exact_pr_fixture : True := by trivial\n"

    def _settings(self, root: Path) -> Settings:
        runtime = root / "toy-apollo"
        artifacts = root / "toy-apollo-artifacts"
        runtime.mkdir()
        artifacts.mkdir()
        (runtime / "inputs").mkdir()
        (runtime / "inputs" / "fixture.tex").write_text(
            "\\begin{theorem}The fixture claim is true.\\end{theorem}\n",
            encoding="utf-8",
        )
        plans = runtime / "plans"
        plans.mkdir()
        phase2 = runtime / "phase2_prompt_packs"
        phase2.mkdir()
        output = runtime / "ToyApollo" / "Output"
        output.mkdir(parents=True)
        return Settings(
            runtime_root=runtime,
            artifact_root=runtime,
            plans_dir=plans,
            reports_dir=runtime / "reports",
            formalized_chapters_dir=runtime / "formalized_chapters",
            output_lean_files_dir=runtime / "output_lean_files",
            phase2_prompt_packs_dir=phase2,
            phase2_softdep_packs_dir=runtime / "phase2_softdep_packs",
            error_logs_dir=runtime / "error_logs",
            toyapollo_output_dir=output,
            aristotle_outbox_dir=runtime / "aristotle_outbox",
            aristotle_archives_dir=runtime / "aristotle_archives",
            mathlib_index_file=runtime / "mathlib_index.faiss",
            mathlib_corpus_file=runtime / "mathlib_corpus.json",
            project_ledger_file=runtime / "project_ledger.json",
            lab_notebook_file=runtime / "lab_notebook.json",
            mathlib_path=runtime / ".lake" / "packages" / "mathlib" / "Mathlib",
            phase0_ingestion_packs_dir=runtime / "phase0_ingestion_packs",
            phase1_prompt_packs_dir=runtime / "phase1_prompt_packs",
            dependency_decisions_dir=runtime / "dependency_decisions",
            workspace_root=root,
            state_db_file=artifacts / "state.sqlite3",
        )

    def _store_with_task(self, settings: Settings) -> WorkspaceStateStore:
        store = WorkspaceStateStore(settings.state_db_file)
        store.initialize()
        store.import_campaign_ledger(
            campaign_id="workspace:active",
            artifact_root=settings.artifact_root,
            legacy_ledger_path=settings.project_ledger_file,
            ledger={
                "tasks": {
                    self.task_id: {
                        "block_id": self.task_id,
                        "type": "Theorem",
                        "title": "Exact PR fixture",
                        "content": "The fixture claim is true.",
                        "source_plan": "fixture",
                        "dependencies": [],
                        "status": "COMPLETED",
                    }
                },
                "symbols": {},
            },
        )
        return store

    def _observation(self, *, head_sha: str = "a" * 40) -> PullRequestObservation:
        subject = SubjectBundle.from_files(
            task_id=self.task_id,
            files={"ProbabilityTheory/chapter_01/thm_1_1.lean": self.code},
            primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
            source_repo="kenneth_pr",
            source_commit=head_sha,
            layout="kenneth",
            subject_kind="github_bundle",
        )
        return PullRequestObservation(
            repo="wkshum/ProbabilityTheory",
            number=9,
            state="open",
            draft=True,
            base_sha="b" * 40,
            head_sha=head_sha,
            head_repo="Kind-NK-Hill/ProbabilityTheory",
            head_ref="agent/exact-review",
            changed_files=(subject.primary_path,),
            affected_files=(subject.primary_path,),
            subject=subject,
            url="https://github.com/wkshum/ProbabilityTheory/pull/9",
        )

    def _prepare(self, root: Path):
        settings = self._settings(root)
        store = self._store_with_task(settings)
        observation = self._observation()
        checkout = root / "checkout"
        primary = checkout / "ProbabilityTheory" / "chapter_01" / "thm_1_1.lean"
        primary.parent.mkdir(parents=True)
        primary.write_text(self.code, encoding="utf-8")

        def observer(repo: str, number: int, task_id: str) -> PullRequestObservation:
            self.assertEqual((repo, number, task_id), (observation.repo, 9, self.task_id))
            return observation

        def verifier(path: Path, current: PullRequestObservation, *, timeout: int):
            self.assertEqual(path, checkout)
            self.assertEqual(current, observation)
            self.assertGreater(timeout, 0)
            return {
                "schema": "toy-apollo.external-pr-build.v1",
                "task_id": self.task_id,
                "repo": observation.repo,
                "pr_number": 9,
                "base_sha": observation.base_sha,
                "head_sha": observation.head_sha,
                "subject_id": observation.subject.subject_id,
                "bundle_hash": observation.subject.bundle_hash,
                "primary_hash": observation.subject.primary_hash,
                "module": "ProbabilityTheory.chapter_01.thm_1_1",
                "command": ["lake", "build", "ProbabilityTheory.chapter_01.thm_1_1"],
                "checkout": str(checkout),
                "success": True,
                "returncode": 0,
                "stdout": "Build completed successfully.",
                "stderr": "",
                "checked_at": "2026-07-18T00:00:00+00:00",
            }

        prepared = prepare_external_pr_review(
            settings=settings,
            store=store,
            repo=observation.repo,
            pr_number=9,
            task_id=self.task_id,
            checkout=checkout,
            observer=observer,
            checkout_verifier=verifier,
        )
        return settings, store, observation, prepared, observer

    def _pass_result(self, prepared: dict) -> dict:
        template = json.loads(
            Path(prepared["review_result_template_file"]).read_text(encoding="utf-8")
        )
        template.update(
            {
                "verdict": "pass",
                "confidence": "high",
                "summary": "Independent exact-head review passed.",
                "proof_class": "source_route_proof_completed",
                "completion_class": "source_route_proof_completed",
                "reviewer_independence": {
                    "role": "independent_read_only_reviewer",
                    "read_only": True,
                    "did_edit_candidate": False,
                    "used_current_review_request": True,
                    "attestation": "Independent test reviewer inspected the exact PR head read-only.",
                },
                "source_claims": [{"claim": "The fixture claim is true."}],
                "claim_mapping": [
                    {"source_claim": "The fixture claim is true.", "lean_declaration": "exact_pr_fixture"}
                ],
                "route_inspection": {
                    "status": "covered",
                    "source_route": "direct proof",
                    "expected_answer_or_statement": "True",
                    "local_mathlib_search": "checked",
                    "public_interface_check": "no public premise",
                    "support_or_reassembly_decision": "none needed",
                    "stop_go_verdict": "go",
                    "notes": "",
                },
                "spine_alignment": {
                    "status": "covered",
                    "summary": "direct proof covered",
                    "source_steps_checked": [
                        {
                            "source_step": "The fixture claim is true.",
                            "lean_landing": "exact_pr_fixture",
                            "status": "covered",
                        }
                    ],
                    "missing_source_steps": [],
                    "shortcut_assessment": "faithful",
                },
                "obligation_review": {
                    "status": "covered",
                    "summary": "no open obligations",
                    "items": [],
                    "open_blockers": [],
                    "scaffold_assessment": [],
                },
                "interface_contract": {"status": "covered", "summary": "covered", "mismatches": []},
                "downstream_adequacy": {
                    "status": "covered",
                    "summary": "covered",
                    "consumers_checked": [],
                    "blocking_issues": [],
                },
                "forbidden_weakenings": [{"status": "not_present", "summary": "none"}],
                "findings": [],
                "recommended_disposition": "promote",
            }
        )
        items = template.get("evidence_review", {}).get("items", [])
        for item in items:
            item["status"] = "covered"
            item["evidence"] = "independent test evidence"
        template["evidence_review"] = {
            "status": "covered",
            "summary": "all required evidence covered",
            "items": items,
            "blocking_issues": [],
        }
        return template

    def test_prepare_binds_exact_pr_bundle_without_creating_toy_candidate(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings, store, observation, prepared, _observer = self._prepare(Path(tmp))
            review_input = json.loads(
                Path(prepared["review_input_file"]).read_text(encoding="utf-8")
            )
            self.assertEqual(review_input["review_subject_kind"], "external_pr")
            self.assertEqual(review_input["subject_bundle"]["bundle_hash"], observation.subject.bundle_hash)
            self.assertEqual(review_input["review_basis"]["external_subject"]["head_sha"], observation.head_sha)
            self.assertFalse((settings.toyapollo_output_dir / f"{self.task_id}.lean").exists())
            self.assertFalse((settings.phase2_prompt_packs_dir / self.task_id / "proof_obligations.json").exists())
            report = store.task_report(self.task_id)
            self.assertEqual(
                report["heads"]["kenneth_pr_head"]["subject_id"], observation.subject.subject_id
            )

    def test_apply_records_clean_pass_only_on_unchanged_exact_head(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings, store, observation, prepared, observer = self._prepare(Path(tmp))
            result_path = Path(prepared["expected_review_result_file"])
            result_path.write_text(
                json.dumps(self._pass_result(prepared), indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            applied = apply_external_pr_review(
                settings=settings,
                store=store,
                metadata_path=Path(prepared["metadata_file"]),
                result_path=result_path,
                observer=observer,
            )
            self.assertTrue(applied["exact_head_covered"])
            self.assertFalse(applied["pr_mutated"])
            coverage = store.review_coverage(observation.subject.subject_id)
            self.assertIsNotNone(coverage)
            self.assertEqual(coverage["authority_scope"], "kenneth_pr_exact_head_review")

    def test_apply_rejects_changed_pr_head_without_recording_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            settings, store, observation, prepared, _observer = self._prepare(Path(tmp))
            result_path = Path(prepared["expected_review_result_file"])
            result_path.write_text(
                json.dumps(self._pass_result(prepared), indent=2, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
            changed = self._observation(head_sha="c" * 40)
            with self.assertRaisesRegex(ExternalPrReviewError, "changed since review preparation"):
                apply_external_pr_review(
                    settings=settings,
                    store=store,
                    metadata_path=Path(prepared["metadata_file"]),
                    result_path=result_path,
                    observer=lambda _repo, _number, _task: changed,
                )
            self.assertIsNone(store.review_coverage(observation.subject.subject_id))

    def test_adopt_binds_completed_pre_cli_exact_review(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings = self._settings(root)
            store = self._store_with_task(settings)
            observation = self._observation()
            evidence_dir = root / "campaign"
            evidence_dir.mkdir()
            review_path = evidence_dir / "semantic_review_result_v1.json"
            review = {
                "schema_version": "toy-apollo.kenneth-pr-exact-semantic-review.v1",
                "task_id": self.task_id,
                "review_subject_file": observation.subject.primary_path,
                "candidate_hash": observation.subject.primary_hash,
                "subject_bundle_hash": observation.subject.bundle_hash,
                "verdict": "pass",
                "reviewer_independence": {
                    "role": "independent read-only reviewer",
                    "read_only": True,
                    "modified_candidate": False,
                    "modified_evidence": False,
                    "created_or_deleted_files": False,
                    "git_checkout_commit_push_performed": False,
                    "build_rerun_by_reviewer": False,
                    "attestation": "independent exact-head review",
                },
                "exact_binding": {
                    "repo": observation.repo,
                    "pull_request": 9,
                    "base_commit": observation.base_sha,
                    "head_commit": observation.head_sha,
                    "changed_files": list(observation.changed_files),
                    "candidate_primary_content_sha256": observation.subject.primary_hash,
                    "exact_pr_bundle_hash": observation.subject.bundle_hash,
                    "integration_head_subject_id": observation.subject.subject_id,
                },
                "question_results": [{"id": "source_fidelity", "status": "pass"}],
            }
            review_path.write_text(json.dumps(review, indent=2), encoding="utf-8")
            import hashlib

            review_hash = hashlib.sha256(review_path.read_bytes()).hexdigest()
            classification_path = evidence_dir / "classification.json"
            classification_path.write_text(
                json.dumps(
                    {
                        "schema_version": "toy-apollo.semantic-review-classification-supplement.v1",
                        "task_id": self.task_id,
                        "basis_review": {"path": str(review_path), "sha256": review_hash},
                        "exact_binding": {
                            "repo": observation.repo,
                            "pull_request": 9,
                            "base_commit": observation.base_sha,
                            "head_commit": observation.head_sha,
                            "candidate_primary_content_sha256": observation.subject.primary_hash,
                            "exact_pr_bundle_hash": observation.subject.bundle_hash,
                            "integration_head_subject_id": observation.subject.subject_id,
                        },
                        "reviewer_independence": {
                            "read_only": True,
                            "lean_tokens_changed": False,
                            "modified_candidate_or_evidence": False,
                        },
                        "verdict": "pass",
                        "proof_class": "textbook_source_route_completed",
                        "completion_class": "textbook_source_route_completed",
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            builder_path = evidence_dir / "builder.json"
            builder_path.write_text(
                json.dumps(
                    {
                        "schema_version": "toy-apollo.kenneth-pr-exact-builder-evidence.v1",
                        "task_id": self.task_id,
                        "exact_subject": {
                            "repo": observation.repo,
                            "pull_request": 9,
                            "base_commit": observation.base_sha,
                            "head_commit": observation.head_sha,
                            "changed_files": list(observation.changed_files),
                            "candidate_primary_content_sha256": observation.subject.primary_hash,
                            "exact_pr_bundle_hash": observation.subject.bundle_hash,
                            "integration_head_subject_id": observation.subject.subject_id,
                        },
                        "checks": {
                            "focused_build": {"exit_code": 0},
                            "forbidden_token_scan": {"exit_code": 0, "findings": {}},
                            "diff_check": {"exit_code": 0},
                            "axiom_probes": {
                                "exit_code": 0,
                                "declarations": {"fixture": ["propext", "Classical.choice", "Quot.sound"]},
                            },
                            "worktree": {"tracked_status": "clean", "head_commit": observation.head_sha},
                            "post_review_remote_refresh": {
                                "state": "OPEN",
                                "is_draft": True,
                                "base_commit": observation.base_sha,
                                "head_commit": observation.head_sha,
                                "changed_files": list(observation.changed_files),
                            },
                        },
                    },
                    indent=2,
                ),
                encoding="utf-8",
            )
            adopted = adopt_external_pr_evidence(
                settings=settings,
                store=store,
                repo=observation.repo,
                pr_number=9,
                task_id=self.task_id,
                review_path=review_path,
                classification_path=classification_path,
                builder_path=builder_path,
                observer=lambda _repo, _number, _task: observation,
            )
            self.assertTrue(adopted["exact_head_covered"])
            coverage = store.review_coverage(observation.subject.subject_id)
            self.assertIsNotNone(coverage)
            self.assertEqual(coverage["authority_scope"], "kenneth_pr_exact_head_review")
            receipt_path = Path(adopted["apply_receipt"])
            self.assertTrue(receipt_path.is_file())
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(receipt["subject_bundle"]["subject_id"], observation.subject.subject_id)

            # Receipts written before subject-manifest persistence are upgraded
            # in place only when every pre-existing field still matches.
            applied_at = receipt["applied_at"]
            for field in ("subject_bundle", "head_repo", "head_ref", "url"):
                receipt.pop(field)
            receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
            adopt_external_pr_evidence(
                settings=settings,
                store=store,
                repo=observation.repo,
                pr_number=9,
                task_id=self.task_id,
                review_path=review_path,
                classification_path=classification_path,
                builder_path=builder_path,
                observer=lambda _repo, _number, _task: observation,
            )
            upgraded = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(upgraded["applied_at"], applied_at)
            self.assertEqual(upgraded["subject_bundle"]["subject_id"], observation.subject.subject_id)

            report = rebuild_workspace_database(
                state_path=settings.state_db_file,
                workspace_root=root,
                runtime_root=settings.runtime_root,
                roots=[evidence_dir],
                refresh_remote=False,
            )
            self.assertEqual(report.external_pr_receipts, 1)
            rebuilt = WorkspaceStateStore(settings.state_db_file)
            rebuilt_coverage = rebuilt.review_coverage(observation.subject.subject_id)
            self.assertIsNotNone(rebuilt_coverage)
            self.assertEqual(
                rebuilt_coverage["authority_scope"], "kenneth_pr_exact_head_review"
            )
            rebuilt_report = rebuilt.task_report(self.task_id)
            self.assertEqual(
                rebuilt_report["heads"]["kenneth_pr_head"]["subject_id"],
                observation.subject.subject_id,
            )


if __name__ == "__main__":
    unittest.main()
