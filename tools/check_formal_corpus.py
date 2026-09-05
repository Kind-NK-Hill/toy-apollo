#!/usr/bin/env python3
"""Verify full corpus build coverage and original or published corpus hashes.

The optional publication map proves export integrity against retained source
hashes. It is not a semantic review, a rebind receipt, or a completion verdict.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
import tomllib


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "ProbabilityTheory"
MANIFEST = ROOT / "manifest_by_chapter.csv"
PROVENANCE = ROOT / "COORDINATION_PROVENANCE.md"
EXPECTED_TOTAL = 584
EXPECTED_CLASSIFICATIONS = {
    "ledger_task_module": 344,
    "task_owned_support_module": 216,
    "shared_support_or_bridge": 24,
}
EXPECTED_TASK_STATUSES = {
    "COMPLETED": 344,
}


def normalized_text(path: Path) -> str:
    return path.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")


def active_lean_text(text: str) -> str:
    """Remove nested comments, line comments, and string contents from Lean source."""
    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False

    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]

        if block_depth:
            if pair == "/-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue

        if in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue

        if pair == "/-":
            block_depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            while index < len(text) and text[index] != "\n":
                result.append(" ")
                index += 1
        elif char == '"':
            in_string = True
            result.append(" ")
            index += 1
        else:
            result.append(char)
            index += 1

    return "".join(result)


def corpus_hash(files: list[Path]) -> str:
    entries: dict[str, str] = {}
    for path in files:
        relative = path.relative_to(ROOT).as_posix()
        digest = hashlib.sha256(normalized_text(path).encode("utf-8")).hexdigest()
        entries[relative] = digest
    return hash_file_entries(entries)


def hash_file_entries(entries: dict[str, str]) -> str:
    """Hash LF-normalized file digests, sorted by repository-relative path."""
    content = "\n".join(f"{path} {entries[path]}" for path in sorted(entries))
    return hashlib.sha256(content.encode("utf-8")).hexdigest()


def build_coverage_errors(config: dict) -> list[str]:
    """Reject a smoke/root-only target even when the manifest is complete."""
    errors = []
    if "ProbabilityTheory" not in config.get("defaultTargets", []):
        errors.append("defaultTargets must include the complete ProbabilityTheory library")
    libraries = [lib for lib in config.get("lean_lib", []) if lib.get("name") == "ProbabilityTheory"]
    if len(libraries) != 1:
        errors.append("expected one ProbabilityTheory Lean library")
    elif libraries[0].get("srcDir", ".") != "." or "ProbabilityTheory.+" not in libraries[0].get("globs", []):
        errors.append("ProbabilityTheory must recursively build ProbabilityTheory.+ from the repository root")
    return errors


def publication_map_errors(
    payload: object,
    *,
    published_files: dict[str, str],
    source_corpus_sha256: str,
    published_corpus_sha256: str,
    source_manifest_sha256: str,
    manifest_sha256: str,
) -> list[str]:
    """Validate both sides of an exhaustive public export map without source text."""
    if not isinstance(payload, dict) or payload.get("schema") != "formalization-engine.public-corpus-map.v1":
        return ["unsupported publication map schema"]
    errors = []
    expected_header = {
        "source_corpus_sha256": source_corpus_sha256,
        "published_corpus_sha256": published_corpus_sha256,
        "source_manifest_sha256": source_manifest_sha256,
        "manifest_sha256": manifest_sha256,
    }
    for key, expected in expected_header.items():
        if payload.get(key) != expected:
            errors.append(f"publication map {key} mismatch")
    rows = payload.get("files")
    if not isinstance(rows, list):
        return [*errors, "publication map files must be a list"]
    source_entries: dict[str, str] = {}
    published_entries: dict[str, str] = {}
    for row in rows:
        if not isinstance(row, dict):
            errors.append("publication map file entry must be an object")
            continue
        path = row.get("path")
        if not isinstance(path, str) or path not in published_files:
            errors.append(f"publication map has an unexpected file path: {path!r}")
            continue
        if path in source_entries:
            errors.append(f"publication map duplicate path: {path}")
            continue
        source_digest = row.get("source_sha256")
        published_digest = row.get("published_sha256")
        if any(not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None for value in (source_digest, published_digest)):
            errors.append(f"publication map invalid SHA-256: {path}")
            continue
        source_entries[path] = source_digest
        published_entries[path] = published_digest
        if published_digest != published_files[path]:
            errors.append(f"publication map published file hash mismatch: {path}")
    if set(source_entries) != set(published_files):
        errors.append("publication map must cover every manifest file exactly once")
    if hash_file_entries(source_entries) != source_corpus_sha256:
        errors.append("publication map source file hashes do not reproduce the retained source corpus hash")
    if hash_file_entries(published_entries) != published_corpus_sha256:
        errors.append("publication map published file hashes do not reproduce the current corpus hash")
    return errors


def fail(message: str) -> None:
    print(f"[FAIL] {message}", file=sys.stderr)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--publication-map", type=Path,
        help="validate a sanitized public export against its complete source/published hash map",
    )
    args = parser.parse_args()
    files = sorted(
        (
            path
            for path in LEAN_ROOT.rglob("*.lean")
            if "Scratch" not in path.relative_to(LEAN_ROOT).parts
        ),
        key=lambda path: path.relative_to(ROOT).as_posix(),
    )
    with MANIFEST.open(newline="", encoding="utf-8-sig") as handle:
        reader = csv.DictReader(handle)
        fields = set(reader.fieldnames or ())
        rows = list(reader)

    required_fields = {"file_path", "module_name"}
    required_fields.update(
        {"basename", "chapter", "sha256"} if args.publication_map is not None else
        {"axiom_count", "sorry_or_admit_in_code", "classification", "ledger_task_match", "ledger_status"}
    )
    if not required_fields <= fields:
        fail(f"manifest is missing required columns: {sorted(required_fields - fields)}")
        return 1
    if args.publication_map is not None and fields != required_fields:
        fail("public manifest must contain only basename, file_path, module_name, chapter, sha256")
        return 1

    errors = 0
    config_errors = build_coverage_errors(tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8")))
    for message in config_errors:
        fail(message)
    errors += len(config_errors)
    actual_paths = [path.relative_to(ROOT).as_posix() for path in files]
    files_by_path = dict(zip(actual_paths, files, strict=True))
    manifest_paths = [row["file_path"].replace("\\", "/") for row in rows]

    if len(files) != EXPECTED_TOTAL:
        fail(f"expected {EXPECTED_TOTAL} Lean modules, found {len(files)}")
        errors += 1
    if len(rows) != EXPECTED_TOTAL:
        fail(f"expected {EXPECTED_TOTAL} manifest rows, found {len(rows)}")
        errors += 1
    if len(set(manifest_paths)) != len(manifest_paths):
        fail("manifest contains duplicate file_path entries")
        errors += 1
    if set(actual_paths) != set(manifest_paths):
        missing = sorted(set(actual_paths) - set(manifest_paths))
        stale = sorted(set(manifest_paths) - set(actual_paths))
        fail(f"manifest/file mismatch; missing={missing}, stale={stale}")
        errors += 1

    for row in rows:
        row_path = row["file_path"].replace("\\", "/")
        expected_module = row_path.removesuffix(".lean").replace("/", ".")
        if row["module_name"] != expected_module:
            fail(f"bad module_name for {row['file_path']}: {row['module_name']}")
            errors += 1
        if "ToyApollo" in row["file_path"] or "ToyApollo" in row["module_name"]:
            fail(f"legacy ToyApollo path in manifest: {row['file_path']}")
            errors += 1

        path = files_by_path.get(row_path)
        if path is not None:
            active_text = active_lean_text(normalized_text(path))
            axiom_count = len(re.findall(r"\baxiom\b", active_text))
            has_placeholder = re.search(r"\b(?:sorry|admit)\b", active_text) is not None
            if args.publication_map is not None:
                if axiom_count or has_placeholder:
                    fail(f"public corpus contains an axiom or proof placeholder: {row_path}")
                    errors += 1
                file_digest = hashlib.sha256(normalized_text(path).encode("utf-8")).hexdigest()
                if row["sha256"] != file_digest:
                    fail(f"public manifest file hash mismatch: {row_path}")
                    errors += 1
                if row["basename"] != path.stem:
                    fail(f"public manifest basename mismatch: {row_path}")
                    errors += 1
            elif row["axiom_count"] != str(axiom_count):
                fail(
                    f"axiom_count mismatch for {row_path}: "
                    f"manifest={row['axiom_count']}, actual={axiom_count}"
                )
                errors += 1
            expected_placeholder = "yes" if has_placeholder else "no"
            if args.publication_map is None and row["sorry_or_admit_in_code"] != expected_placeholder:
                fail(
                    f"sorry/admit mismatch for {row_path}: "
                    f"manifest={row['sorry_or_admit_in_code']}, actual={expected_placeholder}"
                )
                errors += 1

    if args.publication_map is None:
        classifications = Counter(row["classification"] for row in rows)
        if dict(classifications) != EXPECTED_CLASSIFICATIONS:
            fail(f"classification counts changed: {dict(classifications)}")
            errors += 1

        task_statuses = Counter(
            row["ledger_status"] for row in rows if row["ledger_task_match"] == "yes"
        )
        if dict(task_statuses) != EXPECTED_TASK_STATUSES:
            fail(f"task status counts changed: {dict(task_statuses)}")
            errors += 1

    legacy_hits = [
        path.relative_to(ROOT).as_posix()
        for path in files
        if "ToyApollo" in normalized_text(path)
    ]
    if legacy_hits:
        fail(f"legacy ToyApollo references remain in Lean files: {legacy_hits}")
        errors += 1

    digest = corpus_hash(files)
    manifest_digest = hashlib.sha256(normalized_text(MANIFEST).encode("utf-8")).hexdigest()
    provenance = PROVENANCE.read_text(encoding="utf-8")
    match = re.search(
        r"Final coordinated `ProbabilityTheory/` content \| "
        r"584 normalized Lean files, SHA-256 `([0-9a-f]{64})`",
        provenance,
    )
    manifest_match = re.search(
        r"Final manifest \| 584 normalized CSV rows, SHA-256 `([0-9a-f]{64})`",
        provenance,
    )
    if match is None:
        fail("could not locate the final corpus hash in COORDINATION_PROVENANCE.md")
        errors += 1
    elif args.publication_map is not None and manifest_match is not None:
        try:
            payload = json.loads(args.publication_map.read_text(encoding="utf-8"))
            export_errors = publication_map_errors(
                payload,
                published_files={relative: hashlib.sha256(normalized_text(path).encode("utf-8")).hexdigest() for relative, path in files_by_path.items()},
                source_corpus_sha256=match.group(1),
                published_corpus_sha256=digest,
                source_manifest_sha256=manifest_match.group(1),
                manifest_sha256=manifest_digest,
            )
        except (OSError, ValueError) as exc:
            export_errors = [f"cannot read publication map: {exc}"]
        for message in export_errors:
            fail(message)
        errors += len(export_errors)
    elif match.group(1) != digest:
        fail(f"provenance hash is stale: recorded={match.group(1)}, actual={digest}")
        errors += 1

    if manifest_match is None:
        fail("could not locate the manifest hash in COORDINATION_PROVENANCE.md")
        errors += 1
    elif args.publication_map is None and manifest_match.group(1) != manifest_digest:
        fail(
            "manifest hash is stale: "
            f"recorded={manifest_match.group(1)}, actual={manifest_digest}"
        )
        errors += 1

    if errors:
        return 1
    print(
        f"[PASS] {EXPECTED_TOTAL} modules match the manifest; "
        f"corpus SHA-256 {digest}; manifest SHA-256 {manifest_digest}"
    )
    if args.publication_map is not None:
        print("Public export integrity verified; retained source review status is not re-established by this check.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
