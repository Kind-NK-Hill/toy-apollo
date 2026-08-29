import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.block_id_naming import (  # noqa: E402
    canonicalize_block_id,
    canonicalize_task_dict,
    extract_chapter,
    find_block_ids_in_text,
    is_canonical_base_id,
    is_canonical_block_id,
    legacy_ids_for,
    make_derived_id,
    normalize_legacy_id_list,
    resolve_alias,
)


class BlockIdNamingTests(unittest.TestCase):
    def test_canonical_base_id_validation(self):
        self.assertTrue(is_canonical_base_id("def_4_2_inverse_image"))
        self.assertTrue(is_canonical_base_id("ex_4_2_lebesgue_borel"))
        self.assertTrue(is_canonical_base_id("prob_4_13"))
        self.assertFalse(is_canonical_base_id("def_inverse_image"))
        self.assertFalse(is_canonical_base_id("rem_after_def_4_1"))
        self.assertFalse(is_canonical_base_id("def_4_2_main"))

    def test_alias_resolution(self):
        self.assertEqual(resolve_alias("def_inverse_image"), "def_4_2_inverse_image")
        self.assertIn("def_inverse_image", legacy_ids_for("def_4_2_inverse_image"))
        self.assertEqual(resolve_alias("proof_thm_3_3"), "thm_3_3")

    def test_extract_chapter_for_base_and_derived(self):
        self.assertEqual(extract_chapter("def_4_2_inverse_image"), 4)
        self.assertEqual(extract_chapter("def_inverse_image"), 4)
        self.assertEqual(extract_chapter("thm_4_4__lemma_2__main"), 4)

    def test_make_derived_id(self):
        self.assertEqual(make_derived_id("thm_4_4", "lemma", 2), "thm_4_4__lemma_2")
        self.assertEqual(
            make_derived_id("thm_4_4__lemma_2", "main"),
            "thm_4_4__lemma_2__main",
        )

    def test_canonicalize_legacy_derived_ids(self):
        self.assertEqual(canonicalize_block_id("thm_4_4_lemma_3_main"), "thm_4_4__lemma_3__main")
        self.assertEqual(canonicalize_block_id("thm_4_4_step_2"), "thm_4_4__lemma_2")
        self.assertEqual(canonicalize_block_id("def_4_2_main"), "def_4_2__main")
        self.assertEqual(
            canonicalize_block_id("proof_thm_3_3_stieltjes_measure_lemma_1"),
            "thm_3_3__lemma_1",
        )
        self.assertEqual(
            canonicalize_block_id("def_complex_random_variable_complex_rv_lemma_1"),
            "def_4_4_complex_random_variable__lemma_1",
        )

    def test_find_block_ids_in_text(self):
        text = "Use def_inverse_image and def_complex_random_variable before ex_lebesgue_borel."
        found = find_block_ids_in_text(
            text,
            [
                "def_4_2_inverse_image",
                "def_4_4_complex_random_variable",
                "ex_4_2_lebesgue_borel",
            ],
        )
        self.assertEqual(
            found,
            [
                "def_4_2_inverse_image",
                "def_4_4_complex_random_variable",
                "ex_4_2_lebesgue_borel",
            ],
        )

    def test_canonicalize_task_dict(self):
        task = {
            "block_id": "def_inverse_image",
            "dependencies": ["def_sup_inf", "thm_4_7"],
            "soft_imports": ["ex_4_2_1"],
        }
        migrated = canonicalize_task_dict(task)
        self.assertEqual(migrated["block_id"], "def_4_2_inverse_image")
        self.assertEqual(migrated["dependencies"], ["def_4_3_sup_inf", "thm_4_7"])
        self.assertEqual(migrated["soft_imports"], ["ex_4_2_lebesgue_borel"])

    def test_cordis_profile_prefixes(self):
        # cordis per-profile：论文连续编号（def_1 / thm_4 / lem_18 / cor_21）。
        self.assertTrue(is_canonical_base_id("def_1", profile="cordis"))
        self.assertTrue(is_canonical_base_id("thm_4", profile="cordis"))
        self.assertTrue(is_canonical_base_id("lem_18", profile="cordis"))
        self.assertTrue(is_canonical_base_id("cor_21", profile="cordis"))
        self.assertFalse(is_canonical_base_id("def_1", profile="mat"))
        self.assertFalse(is_canonical_base_id("thm_4", profile="mat"))
        self.assertFalse(is_canonical_base_id("intro_9", profile="cordis"))
        self.assertFalse(is_canonical_base_id("lem_x", profile="cordis"))
        self.assertEqual(canonicalize_block_id("thm_4", profile="cordis"), "thm_4")
        self.assertTrue(is_canonical_block_id("lem_18", profile="cordis"))
        self.assertFalse(is_canonical_block_id("lem_18", profile="mat"))

    def test_mat_default_profile_additive_lem_cor_prefixes(self):
        # MAT 默认 profile：加法新增 lem_/cor_ 双段前缀，旧语义不变。
        self.assertTrue(is_canonical_base_id("lem_18_5"))
        self.assertTrue(is_canonical_base_id("cor_21_2"))
        self.assertFalse(is_canonical_base_id("lem_18"))
        self.assertFalse(is_canonical_base_id("cor_21"))
        # 旧前缀行为保持。
        self.assertTrue(is_canonical_base_id("def_4_2_inverse_image"))
        self.assertFalse(is_canonical_base_id("def_4_2_main"))
        self.assertEqual(canonicalize_block_id("thm_4_4_lemma_3_main"), "thm_4_4__lemma_3__main")

    def test_normalize_legacy_id_list_preserves_old_names(self):
        self.assertEqual(
            normalize_legacy_id_list(["def_inverse_image", "def_4_2_inverse_image", "def_inverse_image"]),
            ["def_inverse_image", "def_4_2_inverse_image"],
        )


if __name__ == "__main__":
    unittest.main()
