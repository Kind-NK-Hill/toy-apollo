from __future__ import annotations

import subprocess
from pathlib import Path


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
CONTRACT_PROBE = REPOSITORY_ROOT / "tests" / "lean" / "def_1_2_fin_contract.lean"


def test_def_1_2_fin_contract_compiles() -> None:
    result = subprocess.run(
        ["lake", "env", "lean", str(CONTRACT_PROBE)],
        cwd=REPOSITORY_ROOT,
        capture_output=True,
        text=True,
        timeout=300,
        check=False,
    )

    assert result.returncode == 0, result.stdout + result.stderr
