"""Cordis-profile catalog loading tests.

The first test class exercises ``build_cordis_catalog`` directly with inline
fixtures (no Cordis repository required). The second class loads the real
Cordis policy from ``cordis/data/task_catalog/catalog_policy_v1.json`` and is
skipped until that fixture exists (written by execution-plan step 5.3).
"""

import json
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formalization_engine.task_catalog import (  # noqa: E402
    CatalogError,
    TaskCatalog,
    build_cordis_catalog,
    load_catalog,
    validate_catalog,
)
from formalization_engine.state_migration import rebuild_invariants  # noqa: E402
from formalization_engine.state_store import SubjectBundle, WorkspaceStateStore  # noqa: E402


def _plan_bytes(*entries):
    return json.dumps(entries).encode("utf-8")


class BuildCordisCatalogTests(unittest.TestCase):
    def _module_bytes(self, marker):
        return f"-- {marker}\n".encode("utf-8")

    def test_multi_home_primary_modules_and_counts(self):
        plan = _plan_bytes(
            {"block_id": "def_1", "type": "Definition", "content": "c1", "dependencies": []},
            {"block_id": "def_2", "type": "Definition", "content": "c2", "dependencies": ["def_1"]},
            {"block_id": "thm_4", "type": "Theorem_Statement", "content": "c3", "dependencies": ["def_1", "def_2"]},
            {"block_id": "thm_10", "type": "Theorem_Statement", "content": "c4", "dependencies": ["def_1"]},
        )
        modules = {
            "Cordis/Foundations/EffectContext.lean": self._module_bytes("ctx"),
            "Cordis/Foundations/EffectFunctions.lean": self._module_bytes("fns"),
        }
        task_map = {
            "def_1": "Cordis/Foundations/EffectContext.lean",
            "def_2": "Cordis/Foundations/EffectContext.lean",
            "thm_4": "Cordis/Foundations/EffectContext.lean",
            "thm_10": "Cordis/Foundations/EffectFunctions.lean",
        }
        catalog = build_cordis_catalog(
            catalog_name="cordis-test",
            cordis_commit="0" * 40,
            plan_documents={"plans/sec_test_plan.json": plan},
            module_documents=modules,
            task_module_map=task_map,
            expected_counts={"tasks": 4, "modules": 2, "primary_modules": 2},
        )
        check = validate_catalog(catalog)
        self.assertTrue(check["valid"], check["errors"])
        self.assertEqual(catalog.catalog_id, check["identity_payload_sha256"])
        self.assertEqual(catalog.counts()["tasks"], 4)
        self.assertEqual(catalog.counts()["modules"], 2)
        # Multi-homing: three tasks share one module; bundle = whole module file.
        self.assertEqual(
            catalog.owned_paths("thm_4"),
            ("Cordis/Foundations/EffectContext.lean",),
        )
        self.assertEqual(catalog.owned_paths("thm_4", include_primary=False), ())
        self.assertEqual(
            catalog.owned_paths("thm_10"),
            ("Cordis/Foundations/EffectFunctions.lean",),
        )
        self.assertEqual(len(catalog.task_module_paths), 4)

    def test_fail_closed_on_unknown_module_and_missing_mapping(self):
        plan = _plan_bytes(
            {"block_id": "def_1", "type": "Definition", "content": "c", "dependencies": []},
            {"block_id": "thm_4", "type": "Theorem_Statement", "content": "c", "dependencies": ["def_1"]},
        )
        modules = {"Cordis/Foundations/EffectContext.lean": self._module_bytes("ctx")}
        with self.assertRaises(CatalogError):
            build_cordis_catalog(
                catalog_name="cordis-test",
                cordis_commit="0" * 40,
                plan_documents={"plans/p.json": plan},
                module_documents=modules,
                task_module_map={"def_1": "Cordis/Foundations/Nope.lean", "thm_4": "Cordis/Foundations/EffectContext.lean"},
            )
        with self.assertRaises(CatalogError):
            build_cordis_catalog(
                catalog_name="cordis-test",
                cordis_commit="0" * 40,
                plan_documents={"plans/p.json": plan},
                module_documents=modules,
                task_module_map={"def_1": "Cordis/Foundations/EffectContext.lean"},
            )

    def test_count_invariant_fail_closed(self):
        plan = _plan_bytes(
            {"block_id": "def_1", "type": "Definition", "content": "c", "dependencies": []},
        )
        modules = {"Cordis/Foundations/EffectContext.lean": self._module_bytes("ctx")}
        with self.assertRaises(CatalogError):
            build_cordis_catalog(
                catalog_name="cordis-test",
                cordis_commit="0" * 40,
                plan_documents={"plans/p.json": plan},
                module_documents=modules,
                task_module_map={"def_1": "Cordis/Foundations/EffectContext.lean"},
                expected_counts={"tasks": 99},
            )

    def test_review_distribution_uses_cordis_prompt_namespace(self):
        catalog = build_cordis_catalog(
            catalog_name="cordis-test",
            cordis_commit="0" * 40,
            plan_documents={
                "plans/sec_test_plan.json": _plan_bytes(
                    {
                        "block_id": "thm_4",
                        "type": "Theorem_with_Proof",
                        "content": "Theorem 4 fixture",
                        "dependencies": [],
                    }
                )
            },
            module_documents={
                "Cordis/Foundations/EffectContext.lean": self._module_bytes("ctx")
            },
            task_module_map={"thm_4": "Cordis/Foundations/EffectContext.lean"},
            expected_counts={"tasks": 1, "modules": 1, "primary_modules": 1},
        )
        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "cordis-artifacts" / "state.sqlite3")
            store.initialize()
            store.persist_catalog(catalog)
            subject = SubjectBundle.from_files(
                task_id="thm_4",
                files={"Cordis/Foundations/EffectContext.lean": "theorem t : True := by trivial\n"},
                primary_path="Cordis/Foundations/EffectContext.lean",
                source_repo="cordis",
            )
            store.upsert_subject(subject)
            store.record_review(
                task_id="thm_4",
                subject_id=subject.subject_id,
                verdict="pass",
                proof_class="source_route_theorem",
                completion_class="textbook_source_route_completed",
                phase2_status="pass",
                evidence_path="review.json",
                evidence_hash="a" * 64,
                prompt_version=1,
                rubric_version=1,
            )

            result = rebuild_invariants(store, catalog)

            self.assertEqual(result["compatible_pass"]["all_catalog_found"], 1)
            self.assertEqual(
                result["compatible_pass"]["highest_prompt_distribution_all_catalog_tasks"],
                {1: 1},
            )

    def test_completion_denominator_follows_the_active_catalog(self):
        module_path = "Cordis/Foundations/EffectContext.lean"
        one_task = build_cordis_catalog(
            catalog_name="cordis-test",
            cordis_commit="0" * 40,
            plan_documents={
                "plans/sec_test_plan.json": _plan_bytes(
                    {
                        "block_id": "thm_4",
                        "type": "Theorem_with_Proof",
                        "content": "Theorem 4 fixture",
                        "dependencies": [],
                    }
                )
            },
            module_documents={module_path: self._module_bytes("ctx")},
            task_module_map={"thm_4": module_path},
        )
        two_tasks = build_cordis_catalog(
            catalog_name="cordis-test",
            cordis_commit="1" * 40,
            plan_documents={
                "plans/sec_test_plan.json": _plan_bytes(
                    {
                        "block_id": "def_1",
                        "type": "Definition",
                        "content": "Definition 1 fixture",
                        "dependencies": [],
                    },
                    {
                        "block_id": "thm_4",
                        "type": "Theorem_with_Proof",
                        "content": "Theorem 4 fixture",
                        "dependencies": ["def_1"],
                    },
                )
            },
            module_documents={module_path: self._module_bytes("ctx")},
            task_module_map={"def_1": module_path, "thm_4": module_path},
        )

        with tempfile.TemporaryDirectory() as tmp:
            store = WorkspaceStateStore(Path(tmp) / "cordis-artifacts" / "state.sqlite3")
            store.initialize()

            def land_pass(catalog, task_id):
                subject = SubjectBundle.from_files(
                    task_id=task_id,
                    files={module_path: "theorem t : True := by trivial\n"},
                    primary_path=module_path,
                    source_repo="cordis",
                )
                store.upsert_subject(subject)
                store.set_task_head(
                    task_id=task_id,
                    role="cordis_reviewed",
                    subject_id=subject.subject_id,
                    freshness="fresh",
                )
                store.record_review(
                    task_id=task_id,
                    subject_id=subject.subject_id,
                    verdict="pass",
                    proof_class="source_route_theorem",
                    completion_class="textbook_source_route_completed",
                    phase2_status="pass",
                    evidence_path=f"{task_id}.json",
                    evidence_hash=("a" if task_id == "thm_4" else "b") * 64,
                    reviewer_independence="independent_read_only_reviewer",
                    authority_eligible=True,
                    prompt_version=1,
                    rubric_version=1,
                )

            store.persist_catalog(one_task)
            land_pass(one_task, "thm_4")
            first = rebuild_invariants(store, one_task)
            self.assertTrue(first["all_required_pass"])
            self.assertEqual(first["compatible_pass"]["all_catalog_expected"], 1)
            self.assertEqual(first["exact_current_catalog_bundle_coverage"], 1)

            store.persist_catalog(two_tasks)
            expanded = rebuild_invariants(store, two_tasks)
            self.assertFalse(expanded["all_required_pass"])
            self.assertEqual(expanded["compatible_pass"]["all_catalog_expected"], 2)
            self.assertEqual(expanded["compatible_pass"]["all_catalog_missing"], ["def_1"])

            land_pass(two_tasks, "def_1")
            completed = rebuild_invariants(store, two_tasks)
            self.assertTrue(completed["all_required_pass"])
            self.assertEqual(completed["compatible_pass"]["all_catalog_found"], 2)
            self.assertEqual(completed["exact_current_catalog_bundle_coverage"], 2)


class RealCordisPolicyTests(unittest.TestCase):
    WORKSPACE_ROOT = REPO_ROOT.parent
    CORDIS_ROOT = WORKSPACE_ROOT / "cordis"
    POLICY_PATH = CORDIS_ROOT / "data" / "task_catalog" / "catalog_policy_v1.json"

    def test_load_real_cordis_policy(self):
        if not self.POLICY_PATH.exists():
            self.skipTest("cordis catalog policy fixture not yet written (step 5.3)")
        try:
            catalog = load_catalog(
                workspace_root=self.WORKSPACE_ROOT,
                runtime_root=self.CORDIS_ROOT,
                policy_path=self.POLICY_PATH,
            )
        except CatalogError as exc:
            if "hash mismatch" in str(exc):
                self.skipTest(f"optional external Cordis fixture has drifted: {exc}")
            raise
        self.assertIsInstance(catalog, TaskCatalog)
        check = validate_catalog(catalog)
        self.assertTrue(check["valid"], check["errors"])
        self.assertEqual(check["counts"]["tasks"], 21)
        self.assertEqual(check["counts"]["modules"], 3)
        shared = [t for t, paths in catalog.task_module_paths.items()
                  if paths == ("Cordis/Foundations/EffectContext.lean",)]
        self.assertEqual(len(shared), 7)
        self.assertIn("thm_4", catalog.task_ids())
        self.assertIn("cor_21", catalog.task_ids())


if __name__ == "__main__":
    unittest.main()
