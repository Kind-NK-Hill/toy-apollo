from __future__ import annotations

import json
import unittest
from dataclasses import replace

from src.toy_apollo.task_catalog import CatalogError, build_catalog, validate_catalog


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


if __name__ == "__main__":
    unittest.main()
