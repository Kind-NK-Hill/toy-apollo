from __future__ import annotations

import copy
import hashlib
import unittest

from tools.check_formal_corpus import (
    build_coverage_errors,
    hash_file_entries,
    publication_map_errors,
)


class FullCorpusBuildCoverageTests(unittest.TestCase):
    def test_recursive_library_includes_unimported_consumers(self):
        config = {
            "defaultTargets": ["ProbabilityTheory"],
            "lean_lib": [{"name": "ProbabilityTheory", "globs": ["ProbabilityTheory.+"]}],
        }
        self.assertEqual(build_coverage_errors(config), [])

    def test_smoke_or_root_only_library_is_rejected(self):
        for globs in ([], ["ProbabilityTheory"], ["ProbabilityTheory.chapter_01.+"]):
            with self.subTest(globs=globs):
                config = {
                    "defaultTargets": ["ProbabilityTheory"],
                    "lean_lib": [{"name": "ProbabilityTheory", "globs": globs}],
                }
                self.assertTrue(build_coverage_errors(config))

    def test_default_smoke_target_cannot_replace_the_corpus(self):
        config = {
            "defaultTargets": ["Smoke"],
            "lean_lib": [{"name": "ProbabilityTheory", "globs": ["ProbabilityTheory.+"]}],
        }
        self.assertTrue(build_coverage_errors(config))


class PublicCorpusMapTests(unittest.TestCase):
    def setUp(self):
        self.source = {
            "ProbabilityTheory/chapter_01/definition.lean": self.digest("/- source -/\ndef value := 1\n"),
            "ProbabilityTheory/chapter_02/consumer.lean": self.digest("import ProbabilityTheory.chapter_01.definition\n"),
        }
        self.published = {
            **self.source,
            "ProbabilityTheory/chapter_01/definition.lean": self.digest("def value := 1\n"),
        }
        self.expected = {
            "published_files": self.published,
            "source_corpus_sha256": hash_file_entries(self.source),
            "published_corpus_sha256": hash_file_entries(self.published),
            "source_manifest_sha256": self.digest("original manifest\n"),
            "manifest_sha256": self.digest("public manifest\n"),
        }
        self.payload = {
            "schema": "formalization-engine.public-corpus-map.v1",
            **{key: value for key, value in self.expected.items() if key != "published_files"},
            "files": [
                {"path": path, "source_sha256": self.source[path], "published_sha256": digest}
                for path, digest in self.published.items()
            ],
        }

    @staticmethod
    def digest(text):
        return hashlib.sha256(text.encode("utf-8")).hexdigest()

    def test_comment_only_export_retains_separate_source_and_public_hashes(self):
        self.assertNotEqual(self.expected["source_corpus_sha256"], self.expected["published_corpus_sha256"])
        self.assertEqual(publication_map_errors(self.payload, **self.expected), [])

    def test_missing_consumer_or_duplicate_entry_fails(self):
        for rows in (
            self.payload["files"][:1],
            self.payload["files"] + self.payload["files"][:1],
        ):
            with self.subTest(rows=rows):
                changed = {**self.payload, "files": rows}
                self.assertTrue(publication_map_errors(changed, **self.expected))

    def test_changed_public_code_cannot_use_old_export_map(self):
        actual = {**self.published, "ProbabilityTheory/chapter_01/definition.lean": self.digest("def value := 2\n")}
        expected = {
            **self.expected,
            "published_files": actual,
            "published_corpus_sha256": hash_file_entries(actual),
        }
        self.assertTrue(publication_map_errors(self.payload, **expected))

    def test_forged_source_file_hash_fails_even_with_correct_header(self):
        changed = copy.deepcopy(self.payload)
        changed["files"][0]["source_sha256"] = "a" * 64
        self.assertTrue(publication_map_errors(changed, **self.expected))

    def test_source_manifest_cannot_be_replaced_by_public_manifest(self):
        changed = {**self.payload, "source_manifest_sha256": self.payload["manifest_sha256"]}
        self.assertTrue(publication_map_errors(changed, **self.expected))

    def test_invalid_or_unexpected_map_entry_fails_closed(self):
        for row in (None, {"path": "../outside.lean"}, {"path": next(iter(self.published)), "source_sha256": None}):
            with self.subTest(row=row):
                changed = {**self.payload, "files": [row]}
                self.assertTrue(publication_map_errors(changed, **self.expected))


if __name__ == "__main__":
    unittest.main()
