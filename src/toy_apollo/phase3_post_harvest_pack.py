from __future__ import annotations

import json
import re
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list
from src.compiler import LeanCompiler

from .core import LedgerManager, TaskStatus
from .phase2_prompt_pack import (
    DRAFT_FILE_NAME,
    FAILURE_SUMMARY_FILE_NAME,
    _append_attempt_history,
    _append_verification_report,
    _build_verify_result_payload,
    _compose_detail_text,
    _latest_attempt_summary,
    _load_attempt_history,
    _next_candidate_path,
    _next_verify_result_path,
    _parse_diagnostics,
    _read_file_safely,
    _write_json,
    find_existing_task_file,
    find_task_in_plans,
    has_meaningful_declaration,
    resolve_candidate_path,
    select_latest_verify_result,
)

DECL_FOR_TASK_RE = r"(?ms)^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+{task}\b.*?(?=\s*:=|\s*\bwhere\b)"


def _utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def _normalize_decl_header(text: str) -> str:
    normalized = re.sub(r"\s+", " ", text.strip())
    normalized = normalized.replace("Real.sin", "sin")
    normalized = normalized.replace("Real.cos", "cos")
    normalized = normalized.replace("Filter.limsup", "limsup")
    normalized = normalized.replace("Filter.liminf", "liminf")
    normalized = normalized.replace("Filter.Tendsto", "Tendsto")
    return normalized


def _is_reconciled_statement_ready(metadata: dict[str, Any], candidate_code: str, task_id: str) -> bool:
    chosen_header = str(metadata.get("chosen_reconciled_header", "") or "").strip()
    reconciled_at = str(metadata.get("statement_reconciled_at", "") or "").strip()
    if not chosen_header or not reconciled_at:
        return False
    candidate_header = extract_task_declaration_header(candidate_code, task_id)
    return bool(candidate_header) and candidate_header == _normalize_decl_header(chosen_header)


def extract_task_declaration_header(code: str, task_id: str) -> str:
    if not code.strip():
        return ""
    pattern = re.compile(DECL_FOR_TASK_RE.format(task=re.escape(task_id)))
    match = pattern.search(code)
    return _normalize_decl_header(match.group(0)) if match else ""


def find_latest_staged_task_file(task_id: str, settings) -> Path | None:
    candidates = sorted(
        settings.aristotle_outbox_dir.glob(f"direct_*\\{task_id}\\ToyApollo\\Output\\{task_id}.lean"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    return candidates[0] if candidates else None


def find_latest_summary_file(task_id: str, settings) -> Path | None:
    archive_root = settings.aristotle_archives_dir / task_id / "extracted"
    if not archive_root.exists():
        return None
    candidates = sorted(
        archive_root.rglob("ARISTOTLE_SUMMARY*.md"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    return candidates[0] if candidates else None


def find_latest_verification_log(task_id: str, settings) -> Path | None:
    verify_dir = settings.aristotle_archives_dir / task_id / "verification"
    if not verify_dir.exists():
        return None
    candidates = sorted(
        verify_dir.glob(f"{task_id}_phase3_lake_build.log"),
        key=lambda p: p.stat().st_mtime,
        reverse=True,
    )
    return candidates[0] if candidates else None


def classify_post_harvest_failure(task_id: str, settings) -> dict[str, str]:
    raw_path = settings.aristotle_archives_dir / task_id / "raw" / f"{task_id}.lean"
    staged_path = find_latest_staged_task_file(task_id, settings)
    raw_code = _read_file_safely(raw_path)
    staged_code = _read_file_safely(staged_path) if staged_path else ""

    if not raw_path.exists() or not raw_code.strip() or "sorry" in raw_code:
        return {
            "failure_type": "harvest_missing_clean_file",
            "reason": "Raw harvested file is missing or still contains sorry.",
            "staged_header": extract_task_declaration_header(staged_code, task_id),
            "raw_header": extract_task_declaration_header(raw_code, task_id),
        }

    staged_header = extract_task_declaration_header(staged_code, task_id)
    raw_header = extract_task_declaration_header(raw_code, task_id)
    if staged_header and raw_header and staged_header != raw_header:
        return {
            "failure_type": "statement_drift",
            "reason": "Aristotle raw output changed the task declaration header relative to the staged package.",
            "staged_header": staged_header,
            "raw_header": raw_header,
        }

    return {
        "failure_type": "proof_incomplete",
        "reason": "Task statement matches the staged package; local failure is in proof or implementation details.",
        "staged_header": staged_header,
        "raw_header": raw_header,
    }


def _build_operator_prompt(task: dict[str, Any], failure_type: str) -> str:
    task_id = task["block_id"]
    lines = [
        f"# Post-Harvest Repair Prompt for {task_id}",
        "",
        "You are Codex's local repair agent for exactly one Aristotle-harvested Lean file.",
        "",
        "Rules:",
        "1. Return Lean code only.",
        "2. Edit `draft.lean` as the working file.",
        "3. Treat `raw_candidate.lean` as the exact harvested baseline.",
        "4. Reuse the already-imported local dependencies and do not edit dependency files.",
        "5. Do not redefine Mathlib or local project objects.",
        "6. Use `build_feedback.txt` and `failure_summary.md` before the next attempt.",
        "7. Keep the final result free of `sorry`.",
    ]
    if failure_type == "proof_incomplete":
        lines.extend(
            [
                "8. Preserve the theorem/def statement exactly; repair the proof or implementation body only.",
                "9. Do not weaken or strengthen hypotheses to make the task easier.",
            ]
        )
    else:
        lines.extend(
            [
                "8. This task has statement drift; do not blindly repair the proof against the drifted statement.",
                "9. Reconcile the statement with the textbook semantics before proposing a final candidate.",
                "10. For limsup/liminf sequence problems, prefer chapter-local `seqLimsup` / `seqLiminf` semantics over `Filter.limsup` on `ℝ`.",
            ]
        )
    return "\n".join(lines) + "\n"


def _build_failure_summary(task_id: str, failure_type: str, reason: str, history: dict[str, Any]) -> str:
    latest = _latest_attempt_summary(history)
    lines = [
        f"# Failure Summary for {task_id}",
        "",
        f"- Classified failure type: `{failure_type}`",
        f"- Classification reason: {reason}",
        f"- Recorded repair verify attempts: `{len(history.get('attempts', []))}`",
    ]
    if latest:
        lines.extend(
            [
                f"- Latest attempt status: `{'success' if latest.get('success') else 'failure'}`",
                f"- Latest primary failure kind: `{latest.get('primary_failure_kind', 'none')}`",
            ]
        )
    else:
        lines.append("- Latest attempt status: `(no repair verifications yet)`")
    lines.extend(
        [
            "",
            "Recommended next action:",
            "",
            "- Read `context.md`, then `build_feedback.txt`, then edit `draft.lean`.",
            "- Preserve the staged statement if the failure type is `proof_incomplete`.",
            "- Do not push `statement_drift` tasks through proof repair without reconciling the theorem header first.",
            "",
        ]
    )
    return "\n".join(lines)


def _build_context_markdown(
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    *,
    failure_type: str,
    reason: str,
    staged_path: Path | None,
    raw_path: Path,
    verify_log_path: Path | None,
    summary_path: Path | None,
    staged_header: str,
    raw_header: str,
) -> str:
    task_id = task["block_id"]
    record = ledger.ledger.get("tasks", {}).get(task_id, {})
    snapshot = record.get("candidate_snapshot", {}) if isinstance(record.get("candidate_snapshot"), dict) else {}
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(snapshot.get("soft_imports", []))
    final_union = canonicalize_id_list(hard_deps + soft_imports)
    history = _load_attempt_history(pack_dir, task_id)
    failure_summary_text = _read_file_safely(pack_dir / FAILURE_SUMMARY_FILE_NAME).strip()
    metadata_payload = {}
    metadata_text = _read_file_safely(pack_dir / "metadata.json").strip()
    if metadata_text:
        try:
            metadata_payload = json.loads(metadata_text)
        except Exception:
            metadata_payload = {}
    chosen_header = str(metadata_payload.get("chosen_reconciled_header", "") or "").strip()
    reconciled_at = str(metadata_payload.get("statement_reconciled_at", "") or "").strip()

    lines = [
        f"# Post-Harvest Context for {task_id}",
        "",
        f"- Type: `{task.get('type', 'Unknown')}`",
        f"- Source plan: `{task.get('source_plan', 'unknown')}`",
        f"- Current ledger status: `{record.get('status', 'UNKNOWN')}`",
        f"- Cloud project id: `{record.get('cloud_project_id', '') or '(none)'}`",
        f"- Failure type: `{failure_type}`",
        "",
        "## Original Task",
        "",
        f"### Title\n{task.get('title', '').strip() or '(untitled)'}",
        "",
        "### Content",
        "",
        task.get("content", "").strip() or "(no content)",
        "",
        "## Statement Audit",
        "",
        f"- Classification reason: {reason}",
        f"- Staged theorem header: `{staged_header or '(not found)'}`",
        f"- Raw theorem header: `{raw_header or '(not found)'}`",
        "",
    ]
    if chosen_header:
        lines.extend(
            [
                "## Reconciled Statement",
                "",
                f"- Chosen reconciled header: `{chosen_header}`",
                f"- Statement reconciled at: `{reconciled_at or '(not recorded)'}`",
                "- Proof policy: rewrite under textbook semantics, do not repair drifted Aristotle theorem.",
                "",
            ]
        )
    lines.extend(
        [
        "## Artifacts",
        "",
        f"- Staged file: `{staged_path}`" if staged_path else "- Staged file: `(not found)`",
        f"- Raw harvested file: `{raw_path}`",
        f"- Verification log: `{verify_log_path}`" if verify_log_path else "- Verification log: `(not found)`",
        f"- Aristotle summary: `{summary_path}`" if summary_path else "- Aristotle summary: `(not found)`",
        "",
        "## Hard Dependencies",
        "",
        ]
    )

    if not hard_deps:
        lines.append("- None")
    else:
        for dep_id in hard_deps:
            dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
            dep_file = find_existing_task_file(dep_id, dep_record.get("source_plan", "unknown"), settings)
            lines.append(f"- `{dep_id}`")
            lines.append(f"  - Status: `{dep_record.get('status', 'UNKNOWN')}`")
            lines.append(f"  - File: `{dep_file}`" if dep_file else "  - File: `(not found)`")

    lines.extend(["", "## Soft Imports", ""])
    if not soft_imports:
        lines.append("- None")
    else:
        for dep_id in soft_imports:
            dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
            dep_file = find_existing_task_file(dep_id, dep_record.get("source_plan", "unknown"), settings)
            lines.append(f"- `{dep_id}`")
            lines.append(f"  - Status: `{dep_record.get('status', 'UNKNOWN')}`")
            lines.append(f"  - File: `{dep_file}`" if dep_file else "  - File: `(not found)`")

    lines.extend(["", "## Final Import Union", ""])
    if not final_union:
        lines.append("- None")
    else:
        for dep_id in final_union:
            lines.append(f"- `{dep_id}`")

    build_feedback = _read_file_safely(pack_dir / "build_feedback.txt").strip()
    if build_feedback:
        lines.extend(["", "## Build Feedback", "", "```text", build_feedback, "```", ""])
    summary_excerpt = _read_file_safely(summary_path).strip() if summary_path else ""
    if summary_excerpt:
        lines.extend(["## Aristotle Summary", "", summary_excerpt, ""])
    if failure_summary_text:
        lines.extend(["## Failure Summary", "", failure_summary_text, ""])
    lines.append(f"- Repair verify attempts recorded: `{len(history.get('attempts', []))}`")
    return "\n".join(lines).rstrip() + "\n"


def _refresh_runtime_view(
    task: dict[str, Any],
    ledger: LedgerManager,
    settings,
    pack_dir: Path,
    *,
    failure_type: str,
    reason: str,
    staged_path: Path | None,
    raw_path: Path,
    verify_log_path: Path | None,
    summary_path: Path | None,
    staged_header: str,
    raw_header: str,
) -> None:
    history = _load_attempt_history(pack_dir, task["block_id"])
    existing_metadata = _read_file_safely(pack_dir / "metadata.json").strip()
    existing_payload: dict[str, Any] = {}
    if existing_metadata:
        try:
            existing_payload = json.loads(existing_metadata)
        except Exception:
            existing_payload = {}
    (pack_dir / "failure_summary.md").write_text(
        _build_failure_summary(task["block_id"], failure_type, reason, history),
        encoding="utf-8",
    )
    metadata = {
        "task_id": task["block_id"],
        "failure_type": failure_type,
        "classification_reason": reason,
        "generated_at": _utc_stamp(),
        "hard_dependencies": canonicalize_id_list(task.get("hard_dependencies", task.get("dependencies", []))),
        "soft_imports": canonicalize_id_list(task.get("soft_imports", [])),
        "final_import_union": canonicalize_id_list(task.get("final_import_union", [])),
        "raw_candidate_file": str(raw_path),
        "staged_file": str(staged_path) if staged_path else "",
        "verification_log_file": str(verify_log_path) if verify_log_path else "",
        "summary_file": str(summary_path) if summary_path else "",
        "latest_candidate_file": str((pack_dir / DRAFT_FILE_NAME).resolve()),
        "latest_verify_result_file": str(select_latest_verify_result(pack_dir) or ""),
        "staged_header": staged_header,
        "raw_header": raw_header,
        "chosen_reconciled_header": str(existing_payload.get("chosen_reconciled_header", "") or ""),
        "statement_reconciled_at": str(existing_payload.get("statement_reconciled_at", "") or ""),
    }
    _write_json(pack_dir / "metadata.json", metadata)
    (pack_dir / "context.md").write_text(
        _build_context_markdown(
            task,
            ledger,
            settings,
            pack_dir,
            failure_type=failure_type,
            reason=reason,
            staged_path=staged_path,
            raw_path=raw_path,
            verify_log_path=verify_log_path,
            summary_path=summary_path,
            staged_header=staged_header,
            raw_header=raw_header,
        ),
        encoding="utf-8",
    )


def write_repair_pack(task_id: str, ledger: LedgerManager, settings) -> Path:
    task_id = canonicalize_block_id(task_id)
    if not task_id:
        raise ValueError("Invalid task id for repair-pack.")

    task = find_task_in_plans(task_id, settings.plans_dir)
    if task is None:
        raise FileNotFoundError(f"Task {task_id} was not found in plans/*.json")

    record = ledger.ledger.get("tasks", {}).get(task_id)
    if not isinstance(record, dict):
        raise FileNotFoundError(f"Task {task_id} is missing from the ledger.")
    if record.get("status") not in {TaskStatus.HARVESTED.value, TaskStatus.FAILED_LOCAL.value}:
        raise ValueError(f"repair-pack only supports HARVESTED or FAILED_LOCAL tasks: {task_id}")

    if settings.phase3_post_harvest_packs_dir is None:
        raise ValueError("phase3_post_harvest_packs_dir is not configured.")

    pack_dir = settings.phase3_post_harvest_packs_dir / task_id
    pack_dir.mkdir(parents=True, exist_ok=True)

    raw_path = settings.aristotle_archives_dir / task_id / "raw" / f"{task_id}.lean"
    if not raw_path.exists():
        raise FileNotFoundError(f"Raw harvested file not found: {raw_path}")
    staged_path = find_latest_staged_task_file(task_id, settings)
    verify_log_path = find_latest_verification_log(task_id, settings)
    summary_path = find_latest_summary_file(task_id, settings)
    classification = classify_post_harvest_failure(task_id, settings)
    failure_type = classification["failure_type"]
    reason = classification["reason"]
    staged_header = classification["staged_header"]
    raw_header = classification["raw_header"]

    snapshot = record.get("candidate_snapshot", {}) if isinstance(record.get("candidate_snapshot"), dict) else {}
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(snapshot.get("soft_imports", []))
    final_union = canonicalize_id_list(hard_deps + soft_imports)
    task_payload = {
        "block_id": task_id,
        "type": task.get("type", "Problem"),
        "title": task.get("title", task_id),
        "content": task.get("content", ""),
        "source_plan": task.get("source_plan", "unknown"),
        "hard_dependencies": hard_deps,
        "soft_imports": soft_imports,
        "final_import_union": final_union,
        "failure_type": failure_type,
        "staged_header": staged_header,
        "raw_header": raw_header,
    }
    _write_json(pack_dir / "task.json", task_payload)
    (pack_dir / "operator_prompt.md").write_text(_build_operator_prompt(task_payload, failure_type), encoding="utf-8")
    raw_code = _read_file_safely(raw_path)
    (pack_dir / "raw_candidate.lean").write_text(raw_code, encoding="utf-8")
    draft_path = pack_dir / DRAFT_FILE_NAME
    if not draft_path.exists():
        draft_path.write_text(raw_code, encoding="utf-8")
    if not (pack_dir / "attempt_history.json").exists():
        _write_json(pack_dir / "attempt_history.json", {"task_id": task_id, "attempts": []})
    if not (pack_dir / "verification_report.md").exists():
        (pack_dir / "verification_report.md").write_text(
            f"# Post-Harvest Verification Report for {task_id}\n\n",
            encoding="utf-8",
        )
    build_feedback = _read_file_safely(verify_log_path) if verify_log_path else ""
    (pack_dir / "build_feedback.txt").write_text(build_feedback, encoding="utf-8")

    _refresh_runtime_view(
        task_payload,
        ledger,
        settings,
        pack_dir,
        failure_type=failure_type,
        reason=reason,
        staged_path=staged_path,
        raw_path=raw_path,
        verify_log_path=verify_log_path,
        summary_path=summary_path,
        staged_header=staged_header,
        raw_header=raw_header,
    )
    return pack_dir


async def verify_repair_candidate(task_id: str, ledger: LedgerManager, settings, candidate_arg: str | None = None) -> tuple[bool, str]:
    task_id = canonicalize_block_id(task_id)
    if not task_id:
        raise ValueError("Invalid task id for repair-verify.")
    task = find_task_in_plans(task_id, settings.plans_dir)
    if task is None:
        raise FileNotFoundError(f"Task {task_id} was not found in plans/*.json")
    if settings.phase3_post_harvest_packs_dir is None:
        raise ValueError("phase3_post_harvest_packs_dir is not configured.")

    pack_dir = settings.phase3_post_harvest_packs_dir / task_id
    if not pack_dir.exists():
        raise FileNotFoundError(f"Repair pack directory does not exist: {pack_dir}")

    metadata = json.loads((pack_dir / "metadata.json").read_text(encoding="utf-8"))
    failure_type = str(metadata.get("failure_type", "") or "")
    source_candidate_path = resolve_candidate_path(pack_dir, candidate_arg)
    candidate_code = _read_file_safely(source_candidate_path)
    if failure_type == "statement_drift" and not _is_reconciled_statement_ready(metadata, candidate_code, task_id):
        detail = (
            "repair-verify is blocked because this task was classified as statement_drift. "
            "Reconcile the theorem statement with textbook semantics first."
        )
        return False, detail
    if failure_type == "harvest_missing_clean_file":
        detail = "repair-verify is blocked because the harvested raw file is missing or still contains `sorry`."
        return False, detail

    build_feedback_path = pack_dir / "build_feedback.txt"
    attempt, snapshot_path = _next_candidate_path(pack_dir)
    snapshot_path.write_text(candidate_code, encoding="utf-8")
    verify_result_path = _next_verify_result_path(pack_dir, attempt)
    verified_at = _utc_stamp()

    ledger.update_status(task_id, TaskStatus.VERIFYING)
    ledger.mark_verifying(
        task_id,
        latest_candidate_file=str(snapshot_path),
        verify_attempts=attempt,
    )

    def finalize_failure(
        detail_text: str,
        diagnostics: list[dict[str, Any]],
        *,
        repl_success: bool = False,
        repl_output: str = "",
        temp_build_success: bool = False,
        temp_build_output: str = "",
        final_build_success: bool = False,
        final_build_output: str = "",
    ) -> tuple[bool, str]:
        verify_result = _build_verify_result_payload(
            task_id=task_id,
            attempt=attempt,
            candidate_path=snapshot_path,
            candidate_code=candidate_code,
            verified_at=verified_at,
            repl_success=repl_success,
            repl_output=repl_output,
            temp_build_success=temp_build_success,
            temp_build_output=temp_build_output,
            final_build_success=final_build_success,
            final_build_output=final_build_output,
            diagnostics=diagnostics,
        )
        verify_result["success"] = False
        verify_result["verify_result_file"] = str(verify_result_path)
        _write_json(verify_result_path, verify_result)
        history = _append_attempt_history(pack_dir, task_id, verify_result)
        (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(
            _build_failure_summary(task_id, failure_type, metadata.get("classification_reason", ""), history),
            encoding="utf-8",
        )
        build_feedback_path.write_text(detail_text, encoding="utf-8")
        ledger.update_status(task_id, TaskStatus.FAILED_LOCAL, error=detail_text)
        ledger.mark_verifying(
            task_id,
            latest_candidate_file=str(snapshot_path),
            latest_verify_result_file=str(verify_result_path),
            verify_attempts=attempt,
        )
        _refresh_runtime_view(
            {
                **task,
                "block_id": task_id,
                "hard_dependencies": metadata.get("hard_dependencies", []),
                "soft_imports": metadata.get("soft_imports", []),
                "final_import_union": metadata.get("final_import_union", []),
            },
            ledger,
            settings,
            pack_dir,
            failure_type=failure_type,
            reason=str(metadata.get("classification_reason", "")),
            staged_path=Path(str(metadata.get("staged_file", ""))) if metadata.get("staged_file") else None,
            raw_path=Path(str(metadata.get("raw_candidate_file", ""))),
            verify_log_path=Path(str(metadata.get("verification_log_file", ""))) if metadata.get("verification_log_file") else None,
            summary_path=Path(str(metadata.get("summary_file", ""))) if metadata.get("summary_file") else None,
            staged_header=str(metadata.get("staged_header", "")),
            raw_header=str(metadata.get("raw_header", "")),
        )
        _append_verification_report(pack_dir, verify_result, detail_text)
        return False, detail_text

    if not candidate_code.strip():
        diagnostics = _parse_diagnostics("Candidate file is empty.", "repl_failed", "candidate")
        return finalize_failure("Candidate file is empty.", diagnostics)

    if not has_meaningful_declaration(candidate_code):
        diagnostics = _parse_diagnostics(
            "Candidate does not contain a top-level def/theorem/lemma declaration.",
            "repl_failed",
            "candidate",
        )
        return finalize_failure("Candidate does not contain a top-level def/theorem/lemma declaration.", diagnostics)

    temp_module_basename = f"HarvestRepair_{re.sub(r'[^A-Za-z0-9_]', '_', task_id)}_{attempt}"
    temp_module_file = settings.toyapollo_output_dir / f"{temp_module_basename}.lean"
    temp_module_name = f"ToyApollo.Output.{temp_module_basename}"

    settings.toyapollo_output_dir.mkdir(parents=True, exist_ok=True)
    temp_module_file.write_text(candidate_code, encoding="utf-8")

    compiler = LeanCompiler(root_dir=str(settings.runtime_root))
    repl_success, repl_output = await compiler.validate_with_repl_async(candidate_code)
    temp_build_success, temp_build_output = await compiler.build_module_async(temp_module_name)

    try:
        if repl_success and temp_build_success:
            final_targets = [
                settings.toyapollo_output_dir / f"{task_id}.lean",
                settings.output_lean_files_dir / "general" / f"{task_id}.lean",
            ]
            source_plan = task.get("source_plan", "unknown")
            if source_plan and source_plan != "unknown":
                final_targets.append(settings.output_lean_files_dir / source_plan / f"{task_id}.lean")

            backups: list[tuple[Path, str | None]] = []
            for target in final_targets:
                target.parent.mkdir(parents=True, exist_ok=True)
                backups.append((target, _read_file_safely(target) if target.exists() else None))
                target.write_text(candidate_code, encoding="utf-8")

            final_module_name = f"ToyApollo.Output.{task_id}"
            final_success, final_output = await compiler.build_module_async(final_module_name)
            if not final_success:
                for target, backup_content in backups:
                    if backup_content is None:
                        if target.exists():
                            target.unlink()
                    else:
                        target.write_text(backup_content, encoding="utf-8")
                diagnostics = _parse_diagnostics(final_output, "final_build_failed", "final_build")
                detail_text = _compose_detail_text(repl_output, temp_build_output, final_output)
                return finalize_failure(
                    detail_text,
                    diagnostics,
                    repl_success=repl_success,
                    repl_output=repl_output,
                    temp_build_success=temp_build_success,
                    temp_build_output=temp_build_output,
                    final_build_success=final_success,
                    final_build_output=final_output,
                )

            build_feedback_path.write_text("", encoding="utf-8")
            ledger.register_success(task_id, candidate_code, ledger._hash_text(candidate_code))
            verify_result = _build_verify_result_payload(
                task_id=task_id,
                attempt=attempt,
                candidate_path=snapshot_path,
                candidate_code=candidate_code,
                verified_at=verified_at,
                repl_success=repl_success,
                repl_output=repl_output,
                temp_build_success=temp_build_success,
                temp_build_output=temp_build_output,
                final_build_success=final_success,
                final_build_output=final_output,
                diagnostics=[],
            )
            verify_result["verify_result_file"] = str(verify_result_path)
            _write_json(verify_result_path, verify_result)
            history = _append_attempt_history(pack_dir, task_id, verify_result)
            (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(
                _build_failure_summary(task_id, failure_type, metadata.get("classification_reason", ""), history),
                encoding="utf-8",
            )
            ledger.mark_verifying(
                task_id,
                latest_candidate_file=str(snapshot_path),
                latest_verify_result_file=str(verify_result_path),
                verify_attempts=attempt,
            )
            _refresh_runtime_view(
                {
                    **task,
                    "block_id": task_id,
                    "hard_dependencies": metadata.get("hard_dependencies", []),
                    "soft_imports": metadata.get("soft_imports", []),
                    "final_import_union": metadata.get("final_import_union", []),
                },
                ledger,
                settings,
                pack_dir,
                failure_type=failure_type,
                reason=str(metadata.get("classification_reason", "")),
                staged_path=Path(str(metadata.get("staged_file", ""))) if metadata.get("staged_file") else None,
                raw_path=Path(str(metadata.get("raw_candidate_file", ""))),
                verify_log_path=Path(str(metadata.get("verification_log_file", ""))) if metadata.get("verification_log_file") else None,
                summary_path=Path(str(metadata.get("summary_file", ""))) if metadata.get("summary_file") else None,
                staged_header=str(metadata.get("staged_header", "")),
                raw_header=str(metadata.get("raw_header", "")),
            )
            _append_verification_report(pack_dir, verify_result, "REPL, temporary build, and final build all succeeded.")
            return True, "REPL, temporary build, and final build all succeeded."

        diagnostics = []
        if not repl_success:
            diagnostics.extend(_parse_diagnostics(repl_output, "repl_failed", "repl"))
        if not temp_build_success:
            diagnostics.extend(_parse_diagnostics(temp_build_output, "temp_build_failed", "temp_build"))
        detail_text = _compose_detail_text(repl_output, temp_build_output)
        return finalize_failure(
            detail_text or "Candidate verification failed.",
            diagnostics,
            repl_success=repl_success,
            repl_output=repl_output,
            temp_build_success=temp_build_success,
            temp_build_output=temp_build_output,
        )
    finally:
        if temp_module_file.exists():
            try:
                temp_module_file.unlink()
            except Exception:
                pass
