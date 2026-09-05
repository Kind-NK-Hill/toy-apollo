from __future__ import annotations

import subprocess
import unittest
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
CONTRACT_PROBE = REPOSITORY_ROOT / "tests" / "lean" / "def_1_2_fin_contract.lean"


class Definition12InterfaceTests(unittest.TestCase):
    def test_def_1_2_fin_contract_compiles(self) -> None:
        result = subprocess.run(
            ["lake", "env", "lean", str(CONTRACT_PROBE)],
            cwd=REPOSITORY_ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            timeout=300,
            check=False,
        )

        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
