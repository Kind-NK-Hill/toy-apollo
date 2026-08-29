"""Emit a hash-addressed direct-import manifest for one pinned MAT task."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from src.toy_apollo.state_reconcile import git_file_at_ref  # noqa: E402
from src.toy_apollo.state_store import SubjectBundle  # noqa: E402
from src.toy_apollo.task_catalog import load_catalog  # noqa: E402


def _git(repo: Path, *args: str) -> str:
    done = subprocess.run(["git", "-C", str(repo), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
    if done.returncode not in {0, 1}:
        raise RuntimeError(done.stderr.decode("utf-8", errors="replace").strip())
    return done.stdout.decode("utf-8", errors="replace")


def main() -> int:
    parser = argparse.ArgumentParser(description="Emit current exact MAT direct-import consumers")
    parser.add_argument("--task", required=True)
    parser.add_argument("--workspace-root", type=Path, default=REPO_ROOT.parent)
    parser.add_argument("--runtime-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    catalog = load_catalog(workspace_root=args.workspace_root.resolve(), runtime_root=args.runtime_root.resolve())
    task = next((x for x in catalog.tasks if x.task_id == args.task), None)
    if task is None:
        raise RuntimeError(f"unknown catalog task: {args.task}")
    mat = args.workspace_root.resolve() / "MAT3280-formalization-output"
    head = _git(mat, "rev-parse", "origin/main").strip()
    if head != catalog.mat_commit:
        raise RuntimeError(f"catalog/main mismatch: {catalog.mat_commit} != {head}")
    files = {path: git_file_at_ref(mat, head, path) for path in catalog.owned_paths(args.task)}
    subject = SubjectBundle.from_files(task_id=args.task, files=files, primary_path=task.primary_path, source_repo="mat", source_commit=head, layout="mat", subject_kind="catalog_git_bundle")
    modules = [x.module_name for x in catalog.modules if x.owner_task_id == args.task]
    consumers: dict[str, dict[str, object]] = {}
    for module in modules:
        for line in _git(mat, "grep", "-l", f"^import {module}$", head, "--", "*.lean").splitlines():
            path = line.split(":", 1)[-1].strip()
            owner = catalog.task_for_path(path)
            if owner and owner != args.task:
                consumers.setdefault(owner, {"task_id": owner, "paths": []})["paths"].append(path)
    payload = {"schema": "mat.catalog.direct-consumer-manifest.v1", "task_id": args.task, "commit": head, "subject_id": subject.subject_id, "bundle_hash": subject.bundle_hash, "modules": sorted(modules), "consumers": [consumers[key] for key in sorted(consumers)]}
    output = args.output.resolve()
    if output.exists():
        raise RuntimeError(f"refusing to overwrite: {output}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
