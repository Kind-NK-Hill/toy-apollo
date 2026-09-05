from __future__ import annotations

import json
import unittest
from dataclasses import replace
from pathlib import Path

from formalization_engine.task_catalog import (
    CATALOG_SCHEMA_VERSION_V2,
    LEGACY_CATALOG_SCHEMA_VERSION,
    CatalogError,
    build_catalog,
    load_catalog,
    validate_catalog,
)


class TaskCatalogTests(unittest.TestCase):
    @staticmethod
    def _plan(*entries: tuple[str, str]) -> bytes:
        return json.dumps(
            [
                {
                    "block_id": task_id,
                    "type": task_type,
                    "title": task_id,
                    "content": f"source for {task_id}",
                    "dependencies": [],
                    "source_plan": "fixture",
                }
                for task_id, task_type in entries
            ]
        ).encode("utf-8")

    @staticmethod
    def _manifest(rows: list[tuple[str, str]]) -> bytes:
        header = (
            "group,chapter,file_path,basename,module_name,ledger_task_match,"
            "ledger_status,phase2_status,classification,axiom_count,sorry_or_admit_in_code\n"
        )
        body = "".join(
            f"ProbabilityTheory/chapter_06,6,ProbabilityTheory/chapter_06/{basename}.lean,"
            f"{basename},ProbabilityTheory.chapter_06.{basename},no,,,{role},0,no\n"
            for basename, role in rows
        )
        return (header + body).encode("utf-8")

    def test_formal_plan_task_cannot_be_demoted_by_stale_ledger_match(self):
        plans = {
            "plans/fixture_plan.json": self._plan(
                ("thm_6_7", "Theorem_with_Proof"),
                ("thm_6_7__lemma_1", "Theorem_Statement"),
            )
        }
        manifest = self._manifest(
            [
                ("thm_6_7", "task_owned_support_module"),
                ("thm_6_7__lemma_1", "ledger_task_module"),
                ("thm_6_7_helper", "task_owned_support_module"),
                ("shared_core", "shared_support_or_bridge"),
            ]
        )
        catalog = build_catalog(
            catalog_name="fixture",
            toy_commit="toy",
            mat_commit="mat",
            plan_documents=plans,
            manifest_bytes=manifest,
            family_overrides=[
                {
                    "family_id": "thm_6_7",
                    "book_label": "Theorem 6.7",
                    "family_kind": "split_implementation",
                    "members": ["thm_6_7", "thm_6_7__lemma_1"],
                }
            ],
            restored_task_ids=["thm_6_7"],
            legacy_cohort_id="legacy",
            expected_counts={
                "tasks": 2,
                "families": 1,
                "modules": 4,
                "primary_modules": 2,
                "owned_support_modules": 1,
                "shared_modules": 1,
                "legacy_review_roots": 1,
                "role_migrations": 1,
                "family_overrides": 1,
                "family_override_members": 2,
            },
            mat_tree_paths=[
                "ProbabilityTheory/chapter_06/thm_6_7.lean",
                "ProbabilityTheory/chapter_06/thm_6_7__lemma_1.lean",
                "ProbabilityTheory/chapter_06/thm_6_7_helper.lean",
                "ProbabilityTheory/chapter_06/shared_core.lean",
            ],
        )

        self.assertEqual(catalog.task_ids(), ("thm_6_7", "thm_6_7__lemma_1"))
        self.assertEqual(catalog.task_ids(cohort_id="legacy"), ("thm_6_7__lemma_1",))
        self.assertEqual(catalog.role_migrations, ("thm_6_7",))
        self.assertEqual(
            catalog.owned_paths("thm_6_7"),
            (
                "ProbabilityTheory/chapter_06/thm_6_7.lean",
                "ProbabilityTheory/chapter_06/thm_6_7_helper.lean",
            ),
        )
        self.assertEqual(catalog.family_for_task("thm_6_7__lemma_1").family_id, "thm_6_7")
        self.assertTrue(validate_catalog(catalog)["valid"])
        tampered = replace(catalog, catalog_id="0" * 64)
        check = validate_catalog(tampered)
        self.assertFalse(check["valid"])
        self.assertIn("catalog_id", " ".join(check["errors"]))

    def test_owned_support_without_a_formal_owner_fails_closed(self):
        plans = {
            "plans/fixture_plan.json": self._plan(("def_1_1", "Definition"))
        }
        manifest = self._manifest(
            [
                ("def_1_1", "ledger_task_module"),
                ("unowned_helper", "task_owned_support_module"),
            ]
        )
        with self.assertRaisesRegex(CatalogError, "no formal task owner"):
            build_catalog(
                catalog_name="fixture",
                toy_commit="toy",
                mat_commit="mat",
                plan_documents=plans,
                manifest_bytes=manifest,
                family_overrides=[],
                restored_task_ids=[],
                legacy_cohort_id="legacy",
            )

    def test_real_v2_catalog_is_bound_to_unified_repository_commit(self):
        runtime_root = Path(__file__).resolve().parents[1]
        if not (runtime_root / "data/task_catalog/catalog_policy_v2.json").is_file():
            self.skipTest("requires private unified catalog policy and pinned source fixture")
        catalog = load_catalog(
            workspace_root=runtime_root.parent,
            runtime_root=runtime_root,
        )
        self.assertEqual(catalog.schema_version, CATALOG_SCHEMA_VERSION_V2)
        self.assertEqual(
            catalog.repository_commit,
            "b47b350e72122c1afc9fc2381e4dd1e1873bf1b8",
        )
        self.assertEqual(
            catalog.counts(),
            {
                "tasks": 452,
                "families": 445,
                "modules": 584,
                "primary_modules": 452,
                "owned_support_modules": 108,
                "shared_modules": 24,
                "legacy_review_roots": 344,
                "role_migrations": 108,
                "family_overrides": 5,
                "family_override_members": 12,
            },
        )
        payload = catalog.as_dict()
        self.assertNotIn("toy_commit", payload)
        self.assertNotIn("mat_commit", payload)
        self.assertTrue(validate_catalog(catalog)["valid"])

    def test_real_v1_policy_retains_immutable_catalog_identity(self):
        runtime_root = Path(__file__).resolve().parents[1]
        mat_root = runtime_root.parent / "MAT3280-formalization-output"
        if not (mat_root / ".git").exists() or not (
            runtime_root / "data/task_catalog/catalog_policy_v1.json"
        ).is_file():
            self.skipTest("requires private legacy catalog policy and MAT repository fixture")
        catalog = load_catalog(
            workspace_root=runtime_root.parent,
            runtime_root=runtime_root,
            mat_root=mat_root,
            policy_path=runtime_root
            / "data"
            / "task_catalog"
            / "catalog_policy_v1.json",
        )
        self.assertEqual(catalog.schema_version, LEGACY_CATALOG_SCHEMA_VERSION)
        self.assertEqual(
            catalog.catalog_id,
            "8bb93fd29236bcc05df0abbdf9635b130b2b8e01f1137c8df22ae6f86ae548aa",
        )
        self.assertTrue(validate_catalog(catalog)["valid"])


if __name__ == "__main__":
    unittest.main()
