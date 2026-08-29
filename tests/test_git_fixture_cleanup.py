from __future__ import annotations

import stat
import tempfile
import unittest
from pathlib import Path

from tests.git_fixture_cleanup import remove_git_fixture_tree


class GitFixtureCleanupTests(unittest.TestCase):
    def test_removes_readonly_git_object(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "fixture"
            git_object = root / ".git" / "objects" / "ab" / ("c" * 38)
            git_object.parent.mkdir(parents=True)
            git_object.write_bytes(b"fixture")
            git_object.chmod(stat.S_IREAD)

            remove_git_fixture_tree(root)

            self.assertFalse(root.exists())

    def test_missing_fixture_is_already_clean(self):
        with tempfile.TemporaryDirectory() as tmp:
            remove_git_fixture_tree(Path(tmp) / "missing")


if __name__ == "__main__":
    unittest.main()

