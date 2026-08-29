from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


LOCAL_IMPORT_RE = re.compile(r"(?m)^\s*import\s+ToyApollo\.Output\.([A-Za-z0-9_']+)\s*$")


def _load_json(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def _task_records(root: Path) -> dict[str, Any]:
    payload = _load_json(root / "project_ledger.json", {})
    tasks = payload.get("tasks", {}) if isinstance(payload, dict) else {}
    return tasks if isinstance(tasks, dict) else {}


def _lean_imports(root: Path) -> dict[str, list[str]]:
    output_root = root / "ToyApollo" / "Output"
    imports: dict[str, list[str]] = {}
    if not output_root.exists():
        return imports
    for lean_file in sorted(output_root.glob("*.lean")):
        text = lean_file.read_text(encoding="utf-8", errors="replace")
        local_imports = LOCAL_IMPORT_RE.findall(text)
        if local_imports:
            imports[lean_file.stem] = local_imports
    return imports


def _dependency_manifests(root: Path) -> dict[str, dict[str, Any]]:
    manifests: dict[str, dict[str, Any]] = {}
    for manifest_path in sorted(root.glob("aristotle_outbox/**/dependency_manifest.json")):
        payload = _load_json(manifest_path, {})
        if not isinstance(payload, dict):
            continue
        task_id = str(payload.get("task_id", "") or "")
        if task_id:
            manifests[task_id] = {
                "path": str(manifest_path),
                "hard_dependencies": [entry.get("block_id") for entry in payload.get("hard_dependencies", []) if isinstance(entry, dict)],
                "soft_imports": [entry.get("block_id") for entry in payload.get("soft_imports", []) if isinstance(entry, dict)],
                "final_import_union": [entry.get("block_id") for entry in payload.get("final_import_union", []) if isinstance(entry, dict)],
            }
    return manifests


def build_report(root: Path, task_id: str | None = None) -> str:
    tasks = _task_records(root)
    lean_imports = _lean_imports(root)
    manifests = _dependency_manifests(root)
    task_ids = sorted({*tasks.keys(), *lean_imports.keys(), *manifests.keys()})
    if task_id:
        task_ids = [tid for tid in task_ids if tid == task_id]

    lines = [
        "# Legacy Dependency History Audit",
        "",
        f"- Root: `{root}`",
        f"- Tasks inspected: `{len(task_ids)}`",
        "",
        "All inferred entries are read-only `legacy_inferred` evidence. This tool does not write decision records.",
        "",
    ]
    for tid in task_ids:
        record = tasks.get(tid, {}) if isinstance(tasks.get(tid, {}), dict) else {}
        snapshot = record.get("candidate_snapshot", {}) if isinstance(record.get("candidate_snapshot", {}), dict) else {}
        hard_deps = snapshot.get("dependencies", []) or []
        soft_imports = snapshot.get("soft_imports", []) or []
        imports = lean_imports.get(tid, [])
        manifest = manifests.get(tid, {})
        if not hard_deps and not soft_imports and not imports and not manifest:
            continue
        lines.append(f"## `{tid}`")
        lines.append("")
        lines.append(f"- Ledger hard dependencies: `{', '.join(hard_deps) if hard_deps else '(none)'}`")
        lines.append(f"- Ledger soft imports: `{', '.join(soft_imports) if soft_imports else '(none)'}`")
        lines.append(f"- Final Lean imports: `{', '.join(imports) if imports else '(none)'}`")
        if manifest:
            lines.append(f"- Dependency manifest: `{manifest.get('path', '')}`")
            lines.append(f"- Manifest final union: `{', '.join(manifest.get('final_import_union', [])) or '(none)'}`")
        lines.append("- Suggested criterion: `legacy_inferred_from_output`")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description="Read-only audit of legacy ToyApollo dependency history.")
    parser.add_argument("--root", type=Path, default=Path("."), help="ToyApollo archive/runtime root to inspect.")
    parser.add_argument("--task", type=str, default="", help="Optional task id filter.")
    args = parser.parse_args()
    print(build_report(args.root.resolve(), args.task or None))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
