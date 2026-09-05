#!/usr/bin/env python3
"""Check that every supported chapter can be imported as one Lean environment."""

from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CHAPTERS = (2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14)


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def check_chapter(chapter: int, lake: str) -> bool:
    chapter_dir = ROOT / "ProbabilityTheory" / f"chapter_{chapter:02d}"
    files = sorted(chapter_dir.glob("*.lean"))
    if not files:
        print(f"[FAIL] chapter_{chapter:02d}: no Lean modules found", file=sys.stderr)
        return False

    source = "\n".join(f"import {module_name(path)}" for path in files) + "\n"
    result = subprocess.run(
        [lake, "env", "lean", "--stdin"],
        cwd=ROOT,
        input=source,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode == 0:
        print(f"[PASS] chapter_{chapter:02d}: {len(files)} modules coexist")
        return True

    print(f"[FAIL] chapter_{chapter:02d}: joint import failed", file=sys.stderr)
    if result.stdout:
        print(result.stdout, file=sys.stderr)
    if result.stderr:
        print(result.stderr, file=sys.stderr)
    return False


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "chapters",
        nargs="*",
        type=int,
        default=DEFAULT_CHAPTERS,
        help="chapter numbers to check (default: 2-6 and 8-14)",
    )
    args = parser.parse_args()

    lake = shutil.which("lake")
    if lake is None:
        print("[FAIL] lake is not available on PATH", file=sys.stderr)
        return 1

    failed = [chapter for chapter in args.chapters if not check_chapter(chapter, lake)]
    if failed:
        print("Joint-import failures: " + ", ".join(map(str, failed)), file=sys.stderr)
        return 1

    print(
        "Supported chapter joint-import closure passed. "
        "Chapters 1 and 7 remain the documented Kenneth/Mathlib Partition boundary."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
