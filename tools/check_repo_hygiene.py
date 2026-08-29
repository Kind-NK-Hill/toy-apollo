from __future__ import annotations

import subprocess
import sys
from pathlib import Path


FORBIDDEN_PREFIXES = [
    "output_lean_files/",
    "formalized_chapters/",
    "reports/",
    "error_logs/",
    "error_logs_1/",
    "aristotle_outbox/",
    "aristotle_archives/",
    "aristole-example-outputs/",
]

FORBIDDEN_FILES = {
    "mathlib_index.faiss",
    "mathlib_corpus.json",
    "project_ledger.json",
    "lab_notebook.json",
}


def tracked_files() -> list[str]:
    result = subprocess.run(
        ["git", "ls-files"],
        capture_output=True,
        text=True,
        check=True,
    )
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    bad: list[str] = []
    for f in tracked_files():
        normalized = f.replace("\\", "/")
        if normalized in FORBIDDEN_FILES:
            bad.append(normalized)
            continue
        if any(normalized.startswith(prefix) for prefix in FORBIDDEN_PREFIXES):
            bad.append(normalized)

    if bad:
        print("Repository hygiene check failed. Remove tracked artifacts from main repo:")
        for p in bad:
            print(f" - {p}")
        print(f"Working directory: {root}")
        return 1

    print("Repository hygiene check passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())

