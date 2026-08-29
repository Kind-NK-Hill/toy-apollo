from __future__ import annotations

import argparse
import re
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
HIGH_RISK_SOURCE_MARKERS = (
    TASK_CONTENT_MARKER,
    *LEGACY_SOURCE_MARKERS,
    "Textbook statement",
    "Textbook definition",
)
TASK_FILE_PATTERN = re.compile(r"^(?:def|thm|prob|ex|rem|intro)_", re.IGNORECASE)


@dataclass(frozen=True)
class SanitizeResult:
    text: str
    changed: bool


@dataclass(frozen=True)
class BlockComment:
    start: int
    end: int
    content: str


def block_comments(text: str) -> list[BlockComment]:
    """Return top-level Lean block comments, ignoring strings and line comments."""

    comments: list[BlockComment] = []
    index = 0
    length = len(text)
    while index < length:
        if text.startswith("--", index):
            newline = text.find("\n", index + 2)
            index = length if newline < 0 else newline + 1
            continue

        if text[index] == '"':
            index += 1
            while index < length:
                if text[index] == "\\":
                    index += 2
                    continue
                if text[index] == '"':
                    index += 1
                    break
                index += 1
            continue

        if not text.startswith("/-", index):
            index += 1
            continue

        start = index
        depth = 1
        index += 2
        while index < length and depth:
            if text.startswith("/-", index):
                depth += 1
                index += 2
            elif text.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                index += 1
        if depth:
            raise ValueError("unclosed Lean block comment")
        comments.append(BlockComment(start=start, end=index, content=text[start + 2 : index - 2]))

    return comments


def strip_block_comments(text: str) -> str:
    """Remove Lean block comments while preserving line separation."""

    comments = block_comments(text)
    if not comments:
        return text

    chunks: list[str] = []
    cursor = 0
    for comment in comments:
        chunks.append(text[cursor : comment.start])
        raw = text[comment.start : comment.end]
        chunks.append("\n" if "\n" in raw else " ")
        cursor = comment.end
    chunks.append(text[cursor:])
    return "".join(chunks)


def normalize_code_spacing(text: str) -> str:
    """Remove trailing whitespace and collapse repeated blank code lines."""

    lines: list[str] = []
    previous_blank = False
    for raw_line in text.splitlines():
        line = raw_line.rstrip()
        if not line:
            if previous_blank:
                continue
            previous_blank = True
        else:
            previous_blank = False
        lines.append(line)
    return "\n".join(lines).strip() + "\n"


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
    """Compatibility sanitizer for known legacy markers in support Modules."""

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


def _metadata_lines(text: str, task_id: str) -> list[str]:
    metadata: list[str] = []
    for line in text.splitlines():
        candidate = line.strip()
        if candidate.startswith(METADATA_PREFIXES) and candidate not in metadata:
            metadata.append(candidate)
    if not any(line.startswith("TASK ID:") for line in metadata):
        metadata.insert(0, f"TASK ID: {task_id}")
    return metadata


def sanitize_task_parent(text: str, *, task_id: str) -> SanitizeResult:
    """Create a fail-closed public Task Parent with one uniform source notice.

    Task Parent comments historically mixed implementation notes, generated
    prompts, and source excerpts. Publication keeps executable Lean and line
    comments, but removes every block comment rather than trying to classify
    prose with a growing marker list.
    """

    metadata = _metadata_lines(text, task_id)
    body = normalize_code_spacing(strip_block_comments(text))
    notice = "\n".join(["/-", *metadata, PUBLIC_SOURCE_NOTICE, "-/", ""])
    sanitized = f"{notice}\n{body}"
    return SanitizeResult(text=sanitized, changed=sanitized != text)


def lean_files(output_root: Path) -> list[Path]:
    return sorted(path for path in output_root.rglob("*.lean") if path.is_file())


def is_task_parent(path: Path) -> bool:
    return TASK_FILE_PATTERN.match(path.stem) is not None


def _is_public_notice(comment: BlockComment) -> bool:
    content = comment.content.strip()
    if content.startswith("!"):
        content = content[1:].lstrip()
    lines = [line.strip() for line in content.splitlines() if line.strip()]
    return (
        lines.count(PUBLIC_SOURCE_NOTICE) == 1
        and all(
            line == PUBLIC_SOURCE_NOTICE or line.startswith(METADATA_PREFIXES)
            for line in lines
        )
    )


def task_parent_is_public(text: str) -> bool:
    try:
        comments = block_comments(text)
    except ValueError:
        return False
    return (
        len(comments) == 1
        and _is_public_notice(comments[0])
        and text.count(PUBLIC_SOURCE_NOTICE) == 1
        and not any(marker in text for marker in HIGH_RISK_SOURCE_MARKERS)
    )


def check(output_root: Path) -> list[Path]:
    bad: list[Path] = []
    for path in lean_files(output_root):
        text = path.read_text(encoding="utf-8")
        if is_task_parent(path):
            if not task_parent_is_public(text):
                bad.append(path)
        elif any(marker in text for marker in HIGH_RISK_SOURCE_MARKERS):
            bad.append(path)
    return bad


def apply(output_root: Path) -> tuple[int, int]:
    changed = 0
    scanned = 0
    for path in lean_files(output_root):
        scanned += 1
        original = path.read_text(encoding="utf-8")
        result = (
            sanitize_task_parent(original, task_id=path.stem)
            if is_task_parent(path)
            else sanitize_source_comments(original)
        )
        if not result.changed:
            continue
        path.write_text(result.text, encoding="utf-8", newline="\n")
        changed += 1
    return scanned, changed


def parse_args() -> argparse.Namespace:
    repo_root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(
        description=(
            "Build or verify fail-closed public Lean Task Parents: executable "
            "code plus one uniform source-omission notice, without source prose."
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
        help="Rewrite Task Parents. Without this flag the command checks only.",
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
        print("Public snapshot check failed; non-public Lean Task Parent content remains:")
        for path in remaining:
            print(f" - {path.relative_to(output_root)}")
        return 1

    print("Public snapshot source-excerpt check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
