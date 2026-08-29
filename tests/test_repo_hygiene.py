from __future__ import annotations

import unittest

from tools.check_repo_hygiene import find_forbidden_tracked_files


class RepositoryHygieneTest(unittest.TestCase):
    def test_private_evidence_paths_are_rejected(self) -> None:
        paths = [
            "inputs/chapter.tex",
            "plans/chapter_plan.json",
            "phase2_prompt_packs/def_8_5/metadata.json",
            "docs/archive/old_handoff.md",
            "docs/plans/private-campaign-plan.md",
            "docs/superpowers/specs/private-repair-design.md",
            "docs/phase2_completion_classification.json",
            "data/workspace_inventory/policy_v1.json",
            "upstream/kenneth/f81f1450/def_1_2a.lean",
        ]

        self.assertEqual(find_forbidden_tracked_files(paths), paths)

    def test_curated_public_case_study_is_allowed(self) -> None:
        paths = [
            "examples/case-studies/def_8_5/initial.lean",
            "examples/case-studies/def_8_5/review-timeline.json",
        ]

        self.assertEqual(find_forbidden_tracked_files(paths), [])

    def test_windows_separators_are_normalized(self) -> None:
        self.assertEqual(
            find_forbidden_tracked_files([r"phase2_prompt_packs\def_8_5\task.json"]),
            ["phase2_prompt_packs/def_8_5/task.json"],
        )


if __name__ == "__main__":
    unittest.main()
