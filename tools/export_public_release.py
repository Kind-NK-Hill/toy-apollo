#!/usr/bin/env python3
"""Export a committed, sanitized release tree without copying private Git history.

The destination must be absent or empty. This tool never edits source files or
deletes an existing tree. Commit reviewed changes first; uncommitted changes are
deliberately not exported. Run check_public_release.py inside the exported tree.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
from prepare_public_snapshot import sanitize_task_parent, strip_block_comments
from public_release_policy import selected


def git(root: Path, *args: str) -> bytes:
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True).stdout


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalized(data: bytes) -> bytes:
    try:
        return data.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n").encode("utf-8")
    except UnicodeDecodeError:
        return data


def combined(entries: list[dict], key: str) -> str:
    return digest("\n".join(f"{e['path']} {e[key]}" for e in sorted(entries, key=lambda e: e['path'])).encode())


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode()


def export(root: Path, revision: str, destination: Path) -> dict:
    root, destination = root.resolve(), destination.resolve()
    if destination == root or root in destination.parents:
        raise ValueError("Export destination must be outside the source repository")
    if destination.exists() and any(destination.iterdir()):
        raise ValueError("Destination must be empty; existing exports are preserved")
    commit = git(root, "rev-parse", f"{revision}^{{commit}}").decode().strip()
    paths = git(root, "ls-tree", "-r", "--name-only", "-z", commit).decode().split("\0")
    source = {p: normalized(git(root, "show", f"{commit}:{p}")) for p in paths if p and selected(p)}
    execution_tools = {}
    for name in ("export_public_release.py", "public_release_policy.py", "prepare_public_snapshot.py"):
        path = f"tools/{name}"
        executing = normalized((Path(__file__).resolve().parent / name).read_bytes())
        if source.get(path) != executing:
            raise ValueError(f"Commit the executing publication tool before export: {path}")
        execution_tools[path] = digest(executing)
    source_manifest = source["manifest_by_chapter.csv"]
    rows = list(csv.DictReader(io.StringIO(source_manifest.decode("utf-8-sig"))))
    corpus_entries = []
    transformations: dict[str, str] = {}
    source_hashes = {p: digest(data) for p, data in source.items()}
    for row in rows:
        path = row["file_path"].replace("\\", "/")
        original = source[path].decode("utf-8")
        public = sanitize_task_parent(original, task_id=Path(path).stem).text
        if strip_block_comments(original).strip() != strip_block_comments(public).strip():
            raise ValueError(f"Publication changed executable Lean: {path}")
        source[path] = public.encode("utf-8")
        transformations[path] = "remove_block_prose_preserve_executable_lean"
        corpus_entries.append({"path": path, "source_sha256": source_hashes[path],
                               "published_sha256": digest(source[path])})

    out = io.StringIO(newline="")
    writer = csv.DictWriter(out, fieldnames=["basename", "file_path", "module_name", "chapter", "sha256"], lineterminator="\n")
    writer.writeheader()
    hashes = {e["path"]: e["published_sha256"] for e in corpus_entries}
    for row in rows:
        writer.writerow({**{k: row.get(k, "") for k in ("basename", "file_path", "module_name", "chapter")},
                         "sha256": hashes[row["file_path"].replace("\\", "/")]})
    source["manifest_by_chapter.csv"] = out.getvalue().encode()
    transformations["manifest_by_chapter.csv"] = "build_manifest_without_historical_review_status"
    source_corpus = combined(corpus_entries, "source_sha256")
    source_manifest_hash = digest(source_manifest)
    original_provenance = source["COORDINATION_PROVENANCE.md"].decode()
    if source_corpus not in original_provenance or source_manifest_hash not in original_provenance:
        raise ValueError("Committed source corpus or manifest does not match preserved provenance")
    source["COORDINATION_PROVENANCE.md"] = (
        "# Source snapshot fingerprints\n\n"
        "These fingerprints identify the retained source snapshot before publication.\n"
        "They are historical provenance, not current review verdicts. The public\n"
        "build manifest contains paths and content hashes only. Publication removes\n"
        "block-comment prose while retaining executable Lean; inspect\n"
        "[the file mapping](data/publication/corpus_map.json) for both hashes.\n\n"
        "| Source snapshot | Fingerprint |\n| --- | --- |\n"
        f"| Final coordinated `ProbabilityTheory/` content | {len(rows)} normalized Lean files, SHA-256 `{source_corpus}` |\n"
        f"| Final manifest | {len(rows)} normalized CSV rows, SHA-256 `{source_manifest_hash}` |\n"
    ).encode()
    transformations["COORDINATION_PROVENANCE.md"] = "publish_fingerprints_only"
    corpus_map = {"schema": "formalization-engine.public-corpus-map.v1",
                  "source_commit": commit, "source_corpus_sha256": source_corpus,
                  "published_corpus_sha256": combined(corpus_entries, "published_sha256"),
                  "source_manifest_sha256": source_manifest_hash,
                  "manifest_sha256": digest(source["manifest_by_chapter.csv"]),
                  "authority": "publication_integrity_only_not_semantic_review",
                  "files": corpus_entries}
    source["data/publication/corpus_map.json"] = json_bytes(corpus_map)
    for name in (".gitignore", ".rgignore"):
        source[name] = source.get(name, b"") + b"\n# Private evidence stays outside the public release.\n/inputs/\n/plans/\n/upstream/\n/data/workspace_inventory/\n*.sqlite3\n"
        transformations[name] = "append_public_evidence_exclusions"
    release = {"schema": "formalization-engine.public-release.v1", "source_commit": commit,
               "execution_tools": execution_tools,
               "exporter": "tools/export_public_release.py", "normalization": "UTF-8 LF",
               "authority": "publication_integrity_only_not_semantic_review",
               "files": [{"path": p, "sha256": digest(data),
                          "source_sha256": source_hashes.get(p),
                          "transformation": transformations.get(p, "copy" if p in source_hashes else "generated")}
                         for p, data in sorted(source.items())]}
    source["data/publication/release_manifest.json"] = json_bytes(release)
    destination.mkdir(parents=True, exist_ok=True)
    for p, data in sorted(source.items()):
        target = destination / p
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    return {"source_commit": commit, "files": len(source), "corpus_files": len(corpus_entries),
            "destination": str(destination), "source_corpus_sha256": source_corpus}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--source-ref", default="HEAD")
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    try:
        result = export(args.source_root, args.source_ref, args.destination)
    except (ValueError, OSError, subprocess.CalledProcessError) as exc:
        print(f"Export rejected: {exc}", file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
