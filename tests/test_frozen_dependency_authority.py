import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import AsyncMock, Mock, patch

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.core.sqlite_ledger import SQLiteLedgerManager  # noqa: E402
from src.toy_apollo.cli import app as cli_app  # noqa: E402
from src.toy_apollo.phase2_batch_runner import plan_batch_from_ledger  # noqa: E402
from src.toy_apollo.phase2_dependency_gate import (  # noqa: E402
    FROZEN_DECISION_SCHEMA,
    FROZEN_OWNER_SCOPE,
    FrozenDependencyAuthorityError,
    accept_frozen_dependency_authority,
    build_frozen_dependency_evidence,
    compute_frozen_dependency_basis,
    frozen_dependency_projection,
    revoke_frozen_dependency_authority,
)
from src.toy_apollo.state_reconcile import CommandResult, discover_formal_plan_task_ids  # noqa: E402
from src.toy_apollo.state_store import WorkspaceStateStore, sha256_bytes, sha256_file  # noqa: E402


class FrozenDependencyAuthorityTests(unittest.TestCase):
    def test_formal_plan_discovery_includes_derived_ids_only_for_formal_entries(self):
        with tempfile.TemporaryDirectory() as tmp:
            plans_dir = Path(tmp)
            (plans_dir / "chapter_6_fixture_plan.json").write_text(
                json.dumps(
                    [
                        {"block_id": "thm_6_7__lemma_1", "type": "Theorem_with_Proof"},
                        {"block_id": "rem_6_7_note", "type": "Remark"},
                        {"block_id": "proof_notes_6_7", "type": "Theorem_with_Proof"},
                    ]
                ),
                encoding="utf-8",
            )

            self.assertEqual(
                discover_formal_plan_task_ids(plans_dir, chapters=[6]),
                {"thm_6_7__lemma_1"},
            )

    def _workspace(
        self,
        root: Path,
        *,
        task_id: str = "thm_1_1",
        dependencies=None,
        registered: bool = True,
        semantic_fail: bool = True,
    ):
        dependencies = list(dependencies or [])
        output_dir = root / "ToyApollo" / "Output"
        output_dir.mkdir(parents=True)
        plans_dir = root / "plans"
        plans_dir.mkdir()
        inputs_dir = root / "inputs"
        inputs_dir.mkdir()
        artifact_root = root / "artifacts"
        artifact_root.mkdir()
        phase2_packs = root / "phase2_prompt_packs"
        source_plan = f"chapter_{task_id.split('_')[1]}_fixture"
        content = f"Exact source contract for {task_id}."
        task = {
            "block_id": task_id,
            "type": "Theorem_Statement",
            "content": content,
            "dependencies": dependencies,
            "source_plan": source_plan,
        }
        (plans_dir / f"{source_plan}_plan.json").write_text(
            json.dumps([task]),
            encoding="utf-8",
        )
        (inputs_dir / f"{source_plan}.tex").write_text(
            rf"\begin{{theorem}}{content}\end{{theorem}}",
            encoding="utf-8",
        )
        (output_dir / f"{task_id}.lean").write_text(
            f"theorem {task_id} : True := by trivial\n",
            encoding="utf-8",
        )
        for dependency_id in dependencies:
            (output_dir / f"{dependency_id}.lean").write_text(
                f"theorem {dependency_id} : True := by trivial\n",
                encoding="utf-8",
            )
        record = {
            **task,
            "status": "COMPLETED",
            "candidate_snapshot": dict(task),
        }
        if semantic_fail:
            record.update(
                {
                    "phase2_status": "fail",
                    "phase2_status_reason": "semantic route still fails",
                    "phase2_status_evidence_type": "semantic_review",
                    "phase2_review_verdict": "fail",
                    "phase2_proof_class": "semantic_fail",
                    "stop_reason": "diagnoser_required",
                    "latest_semantic_fail_triage_needs_diagnoser": True,
                    "latest_semantic_fail_triage_local_repair_allowed": False,
                    "failure_events": [
                        {
                            "kind": "semantic_review_fail",
                            "failure_fingerprint": "visible-fail",
                            "canonical_result": True,
                        }
                    ],
                }
            )
        tasks = {task_id: record} if registered else {}
        state_path = root / "state.sqlite3"
        store = WorkspaceStateStore(state_path)
        store.initialize()
        store.import_campaign_ledger(
            campaign_id="workspace:active",
            artifact_root=artifact_root,
            ledger={"tasks": tasks, "symbols": {}},
        )
        legacy_path = artifact_root / "project_ledger.json"
        ledger = SQLiteLedgerManager(
            state_store=store,
            artifact_root=artifact_root,
            legacy_ledger_path=legacy_path,
            campaign_id="workspace:active",
        )
        owner_token = "configured-owner-token"
        settings = SimpleNamespace(
            runtime_root=root,
            artifact_root=artifact_root,
            plans_dir=plans_dir,
            toyapollo_output_dir=output_dir,
            phase2_prompt_packs_dir=phase2_packs,
            state_db_file=state_path,
            frozen_owner_token_sha256=sha256_bytes(owner_token.encode("utf-8")),
        )
        return settings, ledger, owner_token

    def _decision(
        self,
        root: Path,
        settings,
        *,
        task_id: str,
        action: str,
        token: str,
        reason: str,
    ) -> Path:
        payload = {
            "schema_version": FROZEN_DECISION_SCHEMA,
            "action": action,
            "task_id": task_id,
            "owner_scope": FROZEN_OWNER_SCOPE,
            "owner_token_sha256": sha256_bytes(token.encode("utf-8")),
            "reason": reason,
        }
        path = root / f"owner_{action}_{task_id}.json"
        path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")
        return path

    def _build(self, task_id, ledger, settings):
        runner = Mock(return_value=CommandResult(0, b"build ok", b""))
        event = build_frozen_dependency_evidence(
            task_id,
            ledger,
            settings,
            command_runner=runner,
        )
        runner.assert_called_once_with(
            ["lake", "build", f"ToyApollo.Output.{task_id}"],
            cwd=Path(settings.runtime_root),
            timeout=600,
        )
        return event

    def _accept(
        self,
        root: Path,
        task_id: str,
        ledger,
        settings,
        token: str,
        *,
        expected_tip: str = "",
    ):
        build = self._build(task_id, ledger, settings)
        basis = compute_frozen_dependency_basis(task_id, ledger, settings)
        reason = "Owner explicitly froze this completed chapter task."
        decision = self._decision(
            root,
            settings,
            task_id=task_id,
            action="grant",
            token=token,
            reason=reason,
        )
        return accept_frozen_dependency_authority(
            task_id,
            ledger,
            settings,
            owner_scope=FROZEN_OWNER_SCOPE,
            owner_decision_token=token,
            owner_reason=reason,
            owner_decision_path=decision,
            expected_primary_hash=basis.subject.primary_hash,
            expected_subject_hash=basis.subject.bundle_hash,
            expected_dependencies=list(basis.dependencies),
            expected_frozen_tip=expected_tip,
            build_evidence_path=build["evidence_file"],
        )

    def _revoke(self, root, task_id, ledger, settings, token, receipt):
        reason = "Owner explicitly revoked frozen dependency scheduling."
        decision = self._decision(
            root,
            settings,
            task_id=task_id,
            action="revoke",
            token=token,
            reason=reason,
        )
        return revoke_frozen_dependency_authority(
            task_id,
            ledger,
            settings,
            expected_current_receipt=receipt,
            owner_scope=FROZEN_OWNER_SCOPE,
            owner_decision_token=token,
            owner_reason=reason,
            owner_decision_path=decision,
        )

    def test_plan_backed_chapter4_tasks_register_atomically_without_pre_registration(self):
        for task_id in ("thm_4_1", "thm_4_4", "thm_4_5"):
            with self.subTest(task_id=task_id), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                settings, ledger, token = self._workspace(
                    root,
                    task_id=task_id,
                    registered=False,
                )
                self.assertNotIn(task_id, ledger.ledger["tasks"])
                event = self._accept(root, task_id, ledger, settings, token)
                record = ledger.ledger["tasks"][task_id]
                self.assertEqual(record["candidate_snapshot"]["block_id"], task_id)
                self.assertEqual(record["frozen_dependency_receipt_sha256"], event["receipt_sha256"])
                report = WorkspaceStateStore(settings.state_db_file).task_report(task_id)
                self.assertEqual(
                    report["heads"]["frozen_dependency"]["subject_id"],
                    event["subject_id"],
                )
                self.assertEqual(
                    frozen_dependency_projection(
                        task_id,
                        record,
                        ledger,
                        settings,
                    )["phase2_status"],
                    "pass",
                )
                receipt = json.loads(Path(event["receipt_file"]).read_text(encoding="utf-8"))
                self.assertEqual(receipt["owner_scope"], FROZEN_OWNER_SCOPE)
                self.assertEqual(
                    receipt["owner_decision"]["sha256"],
                    sha256_file(Path(receipt["owner_decision"]["file"])),
                )

    def test_harness_owned_build_evidence_is_required_and_state_bound(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings, ledger, token = self._workspace(root)
            basis = compute_frozen_dependency_basis("thm_1_1", ledger, settings)
            arbitrary = root / "arbitrary.json"
            arbitrary.write_text(
                json.dumps(
                    {
                        "schema_version": "toy-apollo.frozen-mechanical-build.v1",
                        "task_id": "thm_1_1",
                        "module": "ToyApollo.Output.thm_1_1",
                        "exit_code": 0,
                        "primary_path": basis.subject.primary_path,
                        "primary_sha256": basis.subject.primary_hash,
                        "subject_bundle_sha256": basis.subject.bundle_hash,
                    }
                ),
                encoding="utf-8",
            )
            reason = "Owner explicitly froze this completed chapter task."
            decision = self._decision(
                root,
                settings,
                task_id="thm_1_1",
                action="grant",
                token=token,
                reason=reason,
            )
            with self.assertRaisesRegex(
                FrozenDependencyAuthorityError,
                "harness-owned",
            ):
                accept_frozen_dependency_authority(
                    "thm_1_1",
                    ledger,
                    settings,
                    owner_scope=FROZEN_OWNER_SCOPE,
                    owner_decision_token=token,
                    owner_reason=reason,
                    owner_decision_path=decision,
                    expected_primary_hash=basis.subject.primary_hash,
                    expected_subject_hash=basis.subject.bundle_hash,
                    expected_dependencies=[],
                    expected_frozen_tip="",
                    build_evidence_path=arbitrary,
                )
            build = self._build("thm_1_1", ledger, settings)
            payload = json.loads(Path(build["evidence_file"]).read_text(encoding="utf-8"))
            run = WorkspaceStateStore(settings.state_db_file).run_record(payload["run_id"])
            self.assertEqual(run["operation"], "frozen_dependency_build_check")
            self.assertEqual(run["status"], "completed")
            self.assertEqual(payload["subject_bundle_sha256"], basis.subject.bundle_hash)

    def test_missing_or_wrong_precommitted_owner_identity_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings, ledger, token = self._workspace(root)
            build = self._build("thm_1_1", ledger, settings)
            basis = compute_frozen_dependency_basis("thm_1_1", ledger, settings)
            reason = "Owner explicitly froze this completed chapter task."
            decision = self._decision(
                root,
                settings,
                task_id="thm_1_1",
                action="grant",
                token=token,
                reason=reason,
            )
            settings.frozen_owner_token_sha256 = ""
            with self.assertRaisesRegex(FrozenDependencyAuthorityError, "missing or invalid"):
                accept_frozen_dependency_authority(
                    "thm_1_1",
                    ledger,
                    settings,
                    owner_scope=FROZEN_OWNER_SCOPE,
                    owner_decision_token=token,
                    owner_reason=reason,
                    owner_decision_path=decision,
                    expected_primary_hash=basis.subject.primary_hash,
                    expected_subject_hash=basis.subject.bundle_hash,
                    expected_dependencies=[],
                    expected_frozen_tip="",
                    build_evidence_path=build["evidence_file"],
                )

    def test_frozen_semantic_fail_and_triage_stay_visible_but_do_not_dominate_consumer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings, ledger, token = self._workspace(root)
            event = self._accept(root, "thm_1_1", ledger, settings, token)
            consumer = {
                "block_id": "thm_1_2",
                "type": "Theorem_Statement",
                "content": "Consumer source contract.",
                "dependencies": ["thm_1_1"],
                "source_plan": "chapter_1_consumer",
            }
            (settings.plans_dir / "chapter_1_consumer_plan.json").write_text(
                json.dumps([consumer]),
                encoding="utf-8",
            )
            (Path(settings.runtime_root) / "inputs" / "chapter_1_consumer.tex").write_text(
                "consumer source",
                encoding="utf-8",
            )
            ledger.add_or_update_task(consumer)
            plan = plan_batch_from_ledger(["thm_1_2"], ledger, settings)
            root_row = next(row for row in plan.report.rows if row.task_id == "thm_1_1")
            consumer_action = next(action for action in plan.actions if action.task_id == "thm_1_2")
            self.assertEqual(root_row.review_verdict, "fail")
            self.assertEqual(root_row.proof_class, "semantic_fail")
            self.assertEqual(root_row.task_status_evidence_type, "frozen_owner_dependency")
            self.assertNotIn("diagnoser", consumer_action.reason)
            self.assertEqual(
                ledger.ledger["tasks"]["thm_1_1"]["failure_events"][0]["failure_fingerprint"],
                "visible-fail",
            )
            self.assertEqual(
                ledger.ledger["tasks"]["thm_1_1"]["frozen_dependency_receipt_sha256"],
                event["receipt_sha256"],
            )

    def test_revoke_is_immediate_idempotent_and_cas_protected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings, ledger, token = self._workspace(root)
            grant = self._accept(root, "thm_1_1", ledger, settings, token)
            stale = SQLiteLedgerManager(
                state_store=WorkspaceStateStore(settings.state_db_file),
                artifact_root=settings.artifact_root,
                legacy_ledger_path=settings.artifact_root / "project_ledger.json",
                campaign_id="workspace:active",
            )
            first = self._revoke(
                root,
                "thm_1_1",
                ledger,
                settings,
                token,
                grant["receipt_sha256"],
            )
            second = self._revoke(
                root,
                "thm_1_1",
                ledger,
                settings,
                token,
                grant["receipt_sha256"],
            )
            self.assertEqual(first, second)
            self.assertEqual(
                frozen_dependency_projection(
                    "thm_1_1",
                    ledger.ledger["tasks"]["thm_1_1"],
                    ledger,
                    settings,
                ),
                {},
            )
            with self.assertRaisesRegex(FrozenDependencyAuthorityError, "CAS"):
                self._revoke(root, "thm_1_1", ledger, settings, token, "0" * 64)
            with self.assertRaises(FrozenDependencyAuthorityError):
                self._revoke(
                    root,
                    "thm_1_1",
                    stale,
                    settings,
                    token,
                    grant["receipt_sha256"],
                )

    def test_stale_revision_rolls_back_campaign_and_normalized_grant(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            settings, ledger, token = self._workspace(root)
            stale = SQLiteLedgerManager(
                state_store=WorkspaceStateStore(settings.state_db_file),
                artifact_root=settings.artifact_root,
                legacy_ledger_path=settings.artifact_root / "project_ledger.json",
                campaign_id="workspace:active",
            )
            build = self._build("thm_1_1", stale, settings)
            basis = compute_frozen_dependency_basis("thm_1_1", stale, settings)
            reason = "Owner explicitly froze this completed chapter task."
            decision = self._decision(
                root,
                settings,
                task_id="thm_1_1",
                action="grant",
                token=token,
                reason=reason,
            )
            ledger.update_runtime_metadata("thm_1_1", concurrent_marker=True)
            with self.assertRaises(FrozenDependencyAuthorityError):
                accept_frozen_dependency_authority(
                    "thm_1_1",
                    stale,
                    settings,
                    owner_scope=FROZEN_OWNER_SCOPE,
                    owner_decision_token=token,
                    owner_reason=reason,
                    owner_decision_path=decision,
                    expected_primary_hash=basis.subject.primary_hash,
                    expected_subject_hash=basis.subject.bundle_hash,
                    expected_dependencies=[],
                    expected_frozen_tip="",
                    build_evidence_path=build["evidence_file"],
                )
            current = WorkspaceStateStore(settings.state_db_file).load_campaign_ledger(
                "workspace:active"
            )[0]["tasks"]["thm_1_1"]
            self.assertNotIn("frozen_dependency_receipt_sha256", current)
            self.assertNotIn(
                "frozen_dependency",
                WorkspaceStateStore(settings.state_db_file).task_report("thm_1_1")["heads"],
            )

    def test_source_lean_dependency_and_receipt_drift_fail_closed(self):
        for drift in ("source", "lean", "dependency", "receipt"):
            with self.subTest(drift=drift), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                settings, ledger, token = self._workspace(
                    root,
                    dependencies=["def_1_0"],
                )
                event = self._accept(root, "thm_1_1", ledger, settings, token)
                record = ledger.ledger["tasks"]["thm_1_1"]
                if drift == "source":
                    (root / "inputs" / "chapter_1_fixture.tex").write_text(
                        "changed source",
                        encoding="utf-8",
                    )
                elif drift == "lean":
                    (settings.toyapollo_output_dir / "thm_1_1.lean").write_text(
                        "theorem thm_1_1 : False := by sorry\n",
                        encoding="utf-8",
                    )
                elif drift == "dependency":
                    (settings.toyapollo_output_dir / "def_1_0.lean").write_text(
                        "theorem def_1_0 : False := by sorry\n",
                        encoding="utf-8",
                    )
                else:
                    receipt = Path(event["receipt_file"])
                    receipt.write_text(
                        receipt.read_text(encoding="utf-8") + " ",
                        encoding="utf-8",
                    )
                self.assertEqual(
                    frozen_dependency_projection("thm_1_1", record, ledger, settings),
                    {},
                )

    def test_cli_parses_build_grant_and_revoke_as_single_task_modes(self):
        cases = (
            (
                "frozen-dependency-build-check",
                [],
            ),
            (
                "frozen-dependency-accept",
                [
                    "--frozen-owner-scope",
                    FROZEN_OWNER_SCOPE,
                    "--frozen-owner-decision-token",
                    "configured-owner-token",
                    "--frozen-owner-reason",
                    "Owner explicitly froze this completed chapter task.",
                    "--frozen-owner-decision",
                    "grant.json",
                    "--expected-primary-hash",
                    "a" * 64,
                    "--expected-subject-hash",
                    "b" * 64,
                    "--expected-dependencies",
                    "",
                    "--expected-frozen-tip",
                    "",
                    "--frozen-build-evidence",
                    "build.json",
                ],
            ),
            (
                "frozen-dependency-revoke",
                [
                    "--frozen-owner-scope",
                    FROZEN_OWNER_SCOPE,
                    "--frozen-owner-decision-token",
                    "configured-owner-token",
                    "--frozen-owner-reason",
                    "Owner explicitly revoked frozen dependency scheduling.",
                    "--frozen-owner-decision",
                    "revoke.json",
                    "--expected-current-frozen-receipt",
                    "c" * 64,
                ],
            ),
        )
        for mode, extra in cases:
            with self.subTest(mode=mode):
                process = AsyncMock()
                argv = [
                    "run_chapter.py",
                    "--phase",
                    "2",
                    "--phase2-mode",
                    mode,
                    "--tasks",
                    "thm_1_1",
                    *extra,
                ]
                with patch.object(sys, "argv", argv), patch.object(
                    cli_app, "process_target", process
                ):
                    self.assertEqual(cli_app.main(), 0)
                args = process.await_args.args[0]
                self.assertEqual(args.phase2_mode, mode)
                self.assertEqual(args.task_ids, ["thm_1_1"])
