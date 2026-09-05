from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from formalization_engine.core.legacy_relocation import LegacyRelocationError, LegacyRelocationMap


class LegacyRelocationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        self.recorded_root = root / "historical-evidence"
        self.current_root = root / "retained-evidence"
        self.current_root.mkdir()
        self.evidence = self.current_root / "state.sqlite3"
        self.evidence.write_bytes(b"retained evidence fixture")
        self.policy = root / "relocation.json"
        self.policy.write_text(
            json.dumps({
                "schema_version": "formalization-engine.legacy-evidence-relocation.v1",
                "mode": "read_only_existing_targets_only",
                "entries": [{
                    "recorded_prefix": self.recorded_root.as_posix(),
                    "current_prefix": self.current_root.as_posix(),
                    "role": "test_evidence",
                }],
            }),
            encoding="utf-8",
        )

    def test_existing_state_database_is_located_without_rewriting_recorded_path(self):
        original_policy = self.policy.read_bytes()
        original_evidence = self.evidence.read_bytes()
        relocation = LegacyRelocationMap.load(self.policy)
        recorded = (self.recorded_root / "state.sqlite3").as_posix()
        target = relocation.locate(recorded)
        self.assertEqual(target, self.evidence.resolve())
        self.assertTrue(target.is_file())
        self.assertFalse(self.recorded_root.exists())
        self.assertEqual(self.policy.read_bytes(), original_policy)
        self.assertEqual(self.evidence.read_bytes(), original_evidence)

    def test_unmapped_path_fails_closed(self):
        relocation = LegacyRelocationMap.load(self.policy)
        with self.assertRaises(LegacyRelocationError):
            relocation.locate(self.policy.parent / "unknown" / "evidence.json")

    def test_missing_target_fails_closed(self):
        relocation = LegacyRelocationMap.load(self.policy)
        with self.assertRaises(LegacyRelocationError):
            relocation.locate(self.recorded_root / "definitely-missing.json")


if __name__ == "__main__":
    unittest.main()
