from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path


TASK_CONTENT_MARKER = "TASK CONTENT:"
PUBLIC_SOURCE_NOTICE = (
    "SOURCE MATERIAL: omitted from the public source snapshot; "
    "see docs/repository_scope.md."
)
METADATA_PREFIXES = ("TASK ID:", "TYPE:", "SOURCE PLAN:")
LEGACY_SOURCE_MARKERS = (
    "\\begin{defbox}",
    "\\begin{thmbox}",
    "\\textbf{",
    "PROVIDED SOLUTION",
)


@dataclass(frozen=True)
class SanitizeResult:
    text: str
    changed: bool


def sanitize_task_header(text: str) -> SanitizeResult:
    sanitized = text
    changed = False
    while True:
        marker_index = sanitized.find(TASK_CONTENT_MARKER)
        if marker_index < 0:
            return SanitizeResult(text=sanitized, changed=changed)

        header_start = sanitized.rfind("/-", 0, marker_index)
        header_end = sanitized.find("-/", marker_index)
        if header_start < 0 or header_end < 0:
            raise ValueError("TASK CONTENT marker is not inside a closed Lean comment")

        header_prefix = sanitized[header_start + 2 : marker_index]
        metadata = [
            line.strip()
            for line in header_prefix.splitlines()
            if line.strip().startswith(METADATA_PREFIXES)
        ]
        replacement_lines = ["/-!", *metadata, PUBLIC_SOURCE_NOTICE, "-/"]
        replacement = "\n".join(replacement_lines)
        sanitized = sanitized[:header_start] + replacement + sanitized[header_end + 2 :]
        changed = True


def sanitize_source_comments(text: str) -> SanitizeResult:
    task_result = sanitize_task_header(text)
    sanitized = task_result.text
    changed = task_result.changed

    while True:
        marker_indexes = [
            index
            for marker in LEGACY_SOURCE_MARKERS
            if (index := sanitized.find(marker)) >= 0
        ]
        if not marker_indexes:
            return SanitizeResult(text=sanitized, changed=changed)

        marker_index = min(marker_indexes)
        comment_start = sanitized.rfind("/-", 0, marker_index)
        comment_end = sanitized.find("-/", marker_index)
        if comment_start < 0 or comment_end < 0:
            raise ValueError("legacy source marker is not inside a closed Lean comment")

        replacement = f"/-!\n{PUBLIC_SOURCE_NOTICE}\n-/"
        sanitized = sanitized[:comment_start] + replacement + sanitized[comment_end + 2 :]
        changed = True


def lean_files(output_root: Path) -> list[Path]:
    return sorted(path for path in output_root.rglob("*.lean") if path.is_file())


def check(output_root: Path) -> list[Path]:
    return [
        path
        for path in lean_files(output_root)
        if any(
            marker in path.read_text(encoding="utf-8")
            for marker in (TASK_CONTENT_MARKER, *LEGACY_SOURCE_MARKERS)
        )
    ]


def apply(output_root: Path) -> tuple[int, int]:
    changed = 0
    scanned = 0
    for path in lean_files(output_root):
        scanned += 1
        original = path.read_text(encoding="utf-8")
        result = sanitize_source_comments(original)
        if not result.changed:
            continue
        path.write_text(result.text, encoding="utf-8", newline="\n")
        changed += 1
    return scanned, changed


def parse_args() -> argparse.Namespace:
    repo_root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(
        description=(
            "Remove embedded TASK CONTENT source excerpts from Lean Task "
            "Parents while preserving task metadata and implementation."
        )
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=repo_root / "ToyApollo" / "Output",
        help="Lean output root to inspect (default: repository ToyApollo/Output)",
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="Rewrite matching headers. Without this flag the command checks only.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    output_root = args.output_root.resolve()
    if not output_root.is_dir():
        print(f"Output root not found: {output_root}")
        return 2

    if args.apply:
        scanned, changed = apply(output_root)
        print(f"Sanitized {changed} of {scanned} Lean files.")

    remaining = check(output_root)
    if remaining:
        print("Public snapshot check failed; embedded TASK CONTENT remains:")
        for path in remaining:
            print(f" - {path.relative_to(output_root)}")
        return 1

    print("Public snapshot source-excerpt check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
