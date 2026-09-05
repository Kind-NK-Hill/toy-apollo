from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from formalization_engine.state_migration import (
    MigrationReport,
    _active_exact_content_target,
    _required_rebuild_invariants,
    discover_evidence_inventory,
    import_review_file,
    rebuild_invariants,
)
from formalization_engine.state_reconcile import refresh_local_repositories
from formalization_engine.state_store import SubjectBundle, WorkspaceStateStore
from formalization_engine.task_catalog import (
    build_catalog,
    build_cordis_catalog,
    validate_catalog_compatible_mat_commit,
)


class StateMigrationInvariantTests(unittest.TestCase):
    @staticmethod
    def _git(repo: Path, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=repo, text=True).strip()

    @classmethod
    def _commit(cls, repo: Path, message: str) -> str:
        subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-qm", message], cwd=repo, check=True)
        return cls._git(repo, "rev-parse", "HEAD")

    @staticmethod
    def _subject_row(subject: SubjectBundle, *, mat_commit: str) -> dict[str, object]:
        return {
            "subject_id": subject.subject_id,
            "task_id": subject.task_id,
            "subject_kind": subject.subject_kind,
            "source_repo": subject.source_repo,
            "source_commit": subject.source_commit,
            "layout": subject.layout,
            "bundle_hash": subject.bundle_hash,
            "primary_hash": subject.primary_hash,
            "primary_path": subject.primary_path,
            "manifest_json": json.dumps(subject.manifest()),
            "mat_commit": mat_commit,
        }

    def test_commit_forward_requires_ancestor_and_exact_full_bundle(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "mat"
            repo.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.email", "fixture@example.com"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.name", "Fixture"], cwd=repo, check=True)
            path = "ProbabilityTheory/chapter_01/thm_1_1.lean"
            (repo / "manifest_by_chapter.csv").write_text("fixture\n", encoding="utf-8")
            lean_path = repo / path
            lean_path.parent.mkdir(parents=True)
            lean_path.write_text("theorem fixture : True := by trivial\n", encoding="utf-8")
            old_commit = self._commit(repo, "old")
            old = SubjectBundle.from_files(
                task_id="thm_1_1", files={path: lean_path.read_bytes()}, primary_path=path,
                source_repo="mat", source_commit=old_commit, layout="mat",
                subject_kind="catalog_git_bundle",
            )
            (repo / "UNRELATED.md").write_text("metadata only\n", encoding="utf-8")
            current_commit = self._commit(repo, "current")
            current = SubjectBundle.from_files(
                task_id="thm_1_1", files={path: lean_path.read_bytes()}, primary_path=path,
                source_repo="mat", source_commit=current_commit, layout="mat",
                subject_kind="catalog_git_bundle",
            )
            resolved, forwarded = _active_exact_content_target(
                old, self._subject_row(current, mat_commit=current_commit),
                target_repo=repo, label="fixture",
            )
            self.assertTrue(forwarded)
            self.assertEqual(resolved.subject_id, current.subject_id)

            changed = SubjectBundle.from_files(
                task_id="thm_1_1", files={path: "theorem fixture : False := by sorry\n"},
                primary_path=path, source_repo="mat", source_commit=current_commit,
                layout="mat", subject_kind="catalog_git_bundle",
            )
            with self.assertRaisesRegex(ValueError, "bundle changed"):
                _active_exact_content_target(
                    old, self._subject_row(changed, mat_commit=current_commit),
                    target_repo=repo, label="fixture",
                )

            subprocess.run(["git", "checkout", "-qb", "side", old_commit], cwd=repo, check=True)
            (repo / "SIDE.md").write_text("side\n", encoding="utf-8")
            side_commit = self._commit(repo, "side")
            side = SubjectBundle.from_files(
                task_id="thm_1_1", files={path: lean_path.read_bytes()}, primary_path=path,
                source_repo="mat", source_commit=side_commit, layout="mat",
                subject_kind="catalog_git_bundle",
            )
            with self.assertRaisesRegex(ValueError, "not an active ancestor"):
                _active_exact_content_target(
                    side, self._subject_row(current, mat_commit=current_commit),
                    target_repo=repo, label="fixture",
                )

    def test_catalog_historical_commit_requires_identical_manifest(self):
        with tempfile.TemporaryDirectory() as tmp:
            repo = Path(tmp) / "mat"
            repo.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.email", "fixture@example.com"], cwd=repo, check=True)
            subprocess.run(["git", "config", "user.name", "Fixture"], cwd=repo, check=True)
            manifest = b"fixture manifest\n"
            (repo / "manifest_by_chapter.csv").write_bytes(manifest)
            old_commit = self._commit(repo, "old")
            (repo / "UNRELATED.md").write_text("metadata only\n", encoding="utf-8")
            current_commit = self._commit(repo, "current")
            catalog = type("Catalog", (), {
                "mat_commit": current_commit,
                "manifest_sha256": hashlib.sha256(manifest).hexdigest(),
            })()
            validate_catalog_compatible_mat_commit(catalog, mat_root=repo, commit=old_commit)

            subprocess.run(["git", "checkout", "-qb", "changed", old_commit], cwd=repo, check=True)
            (repo / "manifest_by_chapter.csv").write_text("changed\n", encoding="utf-8")
            changed_commit = self._commit(repo, "changed manifest")
            catalog.mat_commit = changed_commit
            catalog.manifest_sha256 = hashlib.sha256(b"changed\n").hexdigest()
            with self.assertRaisesRegex(Exception, "different catalog ownership"):
                validate_catalog_compatible_mat_commit(catalog, mat_root=repo, commit=old_commit)

    def test_430_of_452_modern_passes_cannot_satisfy_required_invariants(self):
        required = _required_rebuild_invariants(
            profile="mat",
            catalog_valid=True,
            catalog_counts={"tasks": 452, "families": 445, "modules": 584},
            current_head_count=452,
            compatible_pass_count=430,
            exact_current_count=430,
        )

        self.assertFalse(required["all_catalog_modern_compatible_pass"])
        self.assertFalse(all(required.values()))

    def test_exact_unified_coverage_is_a_required_rebuild_invariant(self):
        required = _required_rebuild_invariants(
            profile="mat",
            catalog_valid=True,
            catalog_counts={"tasks": 452, "families": 445, "modules": 584},
            current_head_count=452,
            compatible_pass_count=452,
            exact_current_count=0,
            unified_catalog=True,
        )

        self.assertFalse(required["all_catalog_exact_current_bundle_coverage"])
        self.assertFalse(all(required.values()))

    @staticmethod
    def _catalog():
        plan = json.dumps(
            [
                {
                    "block_id": "thm_1_1",
                    "type": "Theorem_with_Proof",
                    "title": "Fixture",
                    "content": "The fixture claim.",
                    "dependencies": [],
                    "source_plan": "fixture",
                }
            ]
        ).encode("utf-8")
        manifest = (
            "group,chapter,file_path,basename,module_name,ledger_task_match,"
            "ledger_status,phase2_status,classification,axiom_count,sorry_or_admit_in_code\n"
            "ProbabilityTheory/chapter_01,1,ProbabilityTheory/chapter_01/thm_1_1.lean,"
            "thm_1_1,ProbabilityTheory.chapter_01.thm_1_1,yes,COMPLETED,pass,"
            "ledger_task_module,0,no\n"
        ).encode("utf-8")
        return build_catalog(
            catalog_name="fixture",
            toy_commit="toy",
            mat_commit="mat",
            plan_documents={"plans/fixture_plan.json": plan},
            manifest_bytes=manifest,
            family_overrides=[],
            restored_task_ids=[],
            legacy_cohort_id="legacy",
            mat_tree_paths=["ProbabilityTheory/chapter_01/thm_1_1.lean"],
        )

    def test_compatible_pass_rejects_explicit_nonpass_but_accepts_raw_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "state.sqlite3")
            catalog = self._catalog()
            store.persist_catalog(catalog)
            subject = SubjectBundle.from_files(
                task_id="thm_1_1",
                files={
                    "ProbabilityTheory/chapter_01/thm_1_1.lean":
                        "theorem fixture : True := by trivial\n"
                },
                primary_path="ProbabilityTheory/chapter_01/thm_1_1.lean",
                source_repo="mat",
            )
            store.upsert_subject(subject)
            store.record_review(
                task_id="thm_1_1",
                subject_id=subject.subject_id,
                verdict="pass",
                proof_class="source_route_proof_completed",
                completion_class="source_route_proof_completed",
                phase2_status="inconclusive",
                evidence_path="inconclusive.json",
                evidence_hash="a" * 64,
                prompt_version=11,
                rubric_version=9,
            )

            result = rebuild_invariants(store, catalog)
            self.assertEqual(result["compatible_pass"]["all_catalog_found"], 0)
            self.assertEqual(result["historical_metrics"]["legacy_review_root_compatible_pass"]["found"], 0)

            store.record_review(
                task_id="thm_1_1",
                subject_id=subject.subject_id,
                verdict="pass",
                proof_class="source_route_proof_completed",
                completion_class="source_route_proof_completed",
                phase2_status="",
                evidence_path="raw-pass.json",
                evidence_hash="b" * 64,
                prompt_version=11,
                rubric_version=9,
            )
            result = rebuild_invariants(store, catalog)
            self.assertEqual(result["compatible_pass"]["all_catalog_found"], 1)
            self.assertEqual(result["historical_metrics"]["legacy_review_root_compatible_pass"]["found"], 1)

            store.record_review(
                task_id="thm_1_1",
                subject_id=subject.subject_id,
                verdict="pass",
                proof_class="source_route_proof_completed",
                completion_class="source_route_proof_completed",
                phase2_status="pass",
                evidence_path="pass.json",
                evidence_hash="c" * 64,
                prompt_version=11,
                rubric_version=9,
            )
            result = rebuild_invariants(store, catalog)
            self.assertEqual(result["compatible_pass"]["all_catalog_found"], 1)
            self.assertEqual(result["historical_metrics"]["legacy_review_root_compatible_pass"]["found"], 1)

    def test_inventory_includes_historical_recheck_results_but_not_templates(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            payload = {
                "task_id": "thm_1_1",
                "verdict": "pass",
                "prompt_version": 9,
                "rubric_version": 9,
            }
            recheck = root / "thm_1_1_recheck_result_v3.json"
            recheck.write_text(json.dumps(payload), encoding="utf-8")
            proof_debt = root / "proof_debt_repair_result_v2.json"
            proof_debt.write_text(json.dumps(payload), encoding="utf-8")
            math_review = root / "math_review_result_v1.json"
            math_review.write_text(json.dumps(payload), encoding="utf-8")
            template = root / "semantic_review_result_template.json"
            template.write_text(json.dumps(payload), encoding="utf-8")

            inventory = discover_evidence_inventory([root])
            self.assertIn(recheck.resolve(), inventory.reviews)
            self.assertIn(proof_debt.resolve(), inventory.reviews)
            self.assertIn(math_review.resolve(), inventory.process_events)
            self.assertNotIn(math_review.resolve(), inventory.reviews)
            self.assertNotIn(template.resolve(), inventory.reviews)

    def test_inventory_discovers_authority_relocation_batch_by_schema(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            batch = root / "authority-relocation-batch-v2.json"
            batch.write_text(
                json.dumps(
                    {"schema": "formalization-engine.authority-relocation-batch.v2"}
                ),
                encoding="utf-8",
            )
            decoy = root / "phase5-result.json"
            decoy.write_text(batch.read_text(encoding="utf-8"), encoding="utf-8")

            inventory = discover_evidence_inventory([root])

            self.assertEqual(
                inventory.authority_relocation_batch_receipts, (batch.resolve(),)
            )

    def test_inventory_excludes_release_audit_clean_clones(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            audited_clone = root / "release_audit" / "clean-clone"
            audited_clone.mkdir(parents=True)
            leaked = audited_clone / "authority-relocation-batch-v2.json"
            leaked.write_text(
                json.dumps(
                    {"schema": "formalization-engine.authority-relocation-batch.v2"}
                ),
                encoding="utf-8",
            )

            inventory = discover_evidence_inventory([root])

            self.assertEqual(inventory.authority_relocation_batch_receipts, ())

    def test_cordis_catalog_refresh_uses_profile_current_head(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp)
            runtime = workspace / "cordis"
            runtime.mkdir()
            subprocess.run(["git", "init", "-q"], cwd=runtime, check=True)
            subprocess.run(["git", "config", "user.email", "fixture@example.com"], cwd=runtime, check=True)
            subprocess.run(["git", "config", "user.name", "Fixture"], cwd=runtime, check=True)
            module_path = "Cordis/Foundations/EffectContext.lean"
            lean_path = runtime / module_path
            lean_path.parent.mkdir(parents=True)
            lean_bytes = b"abbrev EffectContext (State : Type) := State\n"
            lean_path.write_bytes(lean_bytes)
            commit = self._commit(runtime, "cordis fixture")
            plan = json.dumps(
                [
                    {
                        "block_id": "def_2",
                        "type": "Definition",
                        "title": "Effect context",
                        "content": "Definition 2 fixture",
                        "dependencies": [],
                        "source_plan": "fixture",
                    }
                ]
            ).encode("utf-8")
            catalog = build_cordis_catalog(
                catalog_name="cordis-test",
                cordis_commit=commit,
                plan_documents={"plans/fixture_plan.json": plan},
                module_documents={module_path: lean_bytes},
                task_module_map={"def_2": module_path},
            )
            store = WorkspaceStateStore(workspace / "cordis-artifacts" / "state.sqlite3")
            store.initialize()

            local = refresh_local_repositories(
                store,
                workspace_root=workspace,
                runtime_root=runtime,
                catalog=catalog,
            )

            self.assertEqual(local["cordis_current"], 1, local)
            with store._connection(write=False) as connection:
                roles = {
                    str(row["role"])
                    for row in connection.execute(
                        "SELECT role FROM task_heads WHERE task_id = ?", ("def_2",)
                    ).fetchall()
                }
            self.assertEqual(roles, {"cordis_current"})

    def test_cordis_review_import_accepts_profile_task_ids(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pack = root / "phase2_prompt_packs" / "def_2"
            pack.mkdir(parents=True)
            subject = SubjectBundle.from_files(
                task_id="def_2",
                files={"official_snapshot_v1.lean": "abbrev EffectContext (State : Type) := State\n"},
                primary_path="official_snapshot_v1.lean",
                source_repo="cordis",
                layout="cordis",
            )
            review_input = {
                "prompt_version": 1,
                "rubric_version": 1,
                "subject_bundle": {
                    "schema": "toy-apollo.subject-bundle.v1",
                    "task_id": subject.task_id,
                    "subject_id": subject.subject_id,
                    "subject_kind": subject.subject_kind,
                    "source_repo": subject.source_repo,
                    "source_commit": subject.source_commit,
                    "layout": subject.layout,
                    "bundle_hash": subject.bundle_hash,
                    "primary_hash": subject.primary_hash,
                    "primary_path": subject.primary_path,
                    "files": subject.manifest(),
                },
            }
            input_path = pack / "semantic_review_input_v1.json"
            input_path.write_text(json.dumps(review_input), encoding="utf-8")
            result = {
                "task_id": "def_2",
                "verdict": "pass",
                "phase2_status": "pass",
                "proof_class": "textbook_definition_completed",
                "completion_class": "definition_only_completed",
                "candidate_hash": subject.primary_hash,
                "review_input_file": str(input_path),
                "review_input_hash": hashlib.sha256(
                    json.dumps(review_input, sort_keys=True, separators=(",", ":")).encode("utf-8")
                ).hexdigest(),
                "prompt_version": 1,
                "rubric_version": 1,
            }
            result_path = pack / "semantic_review_result_v1.json"
            result_path.write_text(json.dumps(result), encoding="utf-8")
            store = WorkspaceStateStore(root / "cordis-artifacts" / "state.sqlite3")
            store.initialize()
            report = MigrationReport(database=str(store.path))

            import_review_file(
                store,
                result_path,
                report,
                applied_receipts={},
                profile="cordis",
            )

            self.assertEqual(report.reviews, 1)
            self.assertEqual(store.summary()["reviews"], 1)


if __name__ == "__main__":
    unittest.main()
