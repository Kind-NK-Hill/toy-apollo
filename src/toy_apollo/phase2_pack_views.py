from __future__ import annotations

import re
from collections import Counter
from pathlib import Path
from typing import Any

from src.block_id_naming import canonicalize_block_id, canonicalize_id_list, extract_chapter

from .core import LedgerManager
from .phase2_pack_shared.artifacts import (
    ATTEMPT_HISTORY_FILE_NAME,
    DRAFT_FILE_NAME,
    FAILURE_SUMMARY_FILE_NAME,
    PROOF_OBLIGATIONS_FILE_NAME,
    REVIEW_REPAIR_REQUEST_PREFIX,
    REVIEW_REPAIR_SUMMARY_PREFIX,
    SEARCH_MANIFEST_FILE_NAME,
    find_existing_task_file,
    intent_contract_path,
    iter_official_output_targets,
    latest_review_repair_request_path,
    latest_review_repair_summary_path,
    list_candidate_files,
    list_versioned_json_files,
    list_versioned_md_files,
    load_attempt_history,
    select_latest_build_result,
    select_latest_candidate,
    select_latest_official_snapshot,
    select_latest_verify_result,
    official_output_candidate_divergence,
)
from .phase2_pack_shared.io import read_file_safely, read_json_safely, sha256_text, write_json
from .phase2_pack_shared.review_basis_parts import (
    build_legacy_intent_contract,
    review_allowed_abstractions,
    review_downstream_checklist,
    review_forbidden_weakenings,
    review_history_risks,
    review_spine_contract,
)
from .phase2_pack_shared.runtime_state import (
    auto_loop_state_from_record,
    count_consecutive_primary_failures,
    recommended_action_for_kind,
)
from .phase2_proof_obligations import (
    maybe_ensure_proof_obligations_file,
    render_proof_obligations_markdown,
    summarize_proof_obligations,
)
from .phase2_review_request import _latest_review_request_path, _collect_direct_downstream_consumers
from .phase2_semantic_review import (
    latest_semantic_review_artifact_paths,
    latest_semantic_review_context_path,
    render_semantic_review_report as _semantic_review_report,
)


def _auto_loop_next_action(current_record: dict[str, Any] | None) -> str:
    if isinstance(current_record, dict) and {"enabled", "phase", "status"}.issubset(current_record.keys()):
        state = {
            "enabled": bool(current_record.get("enabled")),
            "phase": str(current_record.get("phase", "") or ""),
            "status": str(current_record.get("status", "") or ""),
        }
    else:
        state = auto_loop_state_from_record(current_record)
    if not state["enabled"] or state["status"] != "active":
        return ""
    if state["phase"] in {"review_prepared", "reviewing"}:
        return "reviewer_write_result"
    if state["phase"] in {"applying", "repair_seeded"}:
        return "runtime_apply_or_repair"
    return "author_continue"


def _auto_loop_stop_reason_note(stop_reason: str) -> str:
    reason = str(stop_reason or "").strip().lower()
    if reason == "nonprogress":
        return (
            "Semantic non-progress means the loop has repeated the same semantic review failure "
            "or the same candidate content across auto-loop rounds without a meaningful fix."
        )
    return ""


def _resolve_pack_path(raw_path: str, pack_dir: Path) -> Path:
    path = Path(raw_path).expanduser()
    if not path.is_absolute():
        path = (pack_dir / path).resolve()
    return path


def _official_output_route_note(task: dict[str, Any], current_record: dict[str, Any], settings, pack_dir: Path) -> str:
    ready_raw = str(current_record.get("latest_build_ready_candidate_file", "") or "").strip()
    if not ready_raw:
        return ""
    ready_path = _resolve_pack_path(ready_raw, pack_dir)
    if not ready_path.exists():
        return ""
    divergence = official_output_candidate_divergence(
        task_id=task["block_id"],
        source_plan=str(task.get("source_plan", "unknown") or "unknown"),
        settings=settings,
        candidate_path=ready_path,
        candidate_hash=str(current_record.get("latest_build_ready_candidate_hash", "") or ""),
        draft_path=pack_dir / DRAFT_FILE_NAME,
    )
    if divergence.get("official_supersedes_candidate"):
        return (
            "Official output is newer than and differs from the latest build-ready candidate. "
            "Use `review-now --review-subject existing` to review the repaired official output, "
            "or sync the official output into `draft.lean` and rerun `build-check` before candidate review."
        )
    if divergence.get("official_differs_from_candidate"):
        return (
            "Official output differs from the latest build-ready candidate. Continue candidate review only "
            "when this is an active draft/build-check repair; use `review-now --review-subject existing` "
            "when auditing the already-runnable output."
        )
    return ""


def build_operator_prompt(
    task: dict[str, Any],
    ledger: LedgerManager | None = None,
    settings=None,
    pack_dir: Path | None = None,
) -> str:
    task_id = task["block_id"]
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {}) if ledger is not None else {}
    auto_loop_state = auto_loop_state_from_record(current_record if isinstance(current_record, dict) else {})
    review_mode_active = (
        auto_loop_state["enabled"]
        and auto_loop_state["status"] == "active"
        and auto_loop_state["phase"] in {"review_prepared", "reviewing", "applying"}
        and bool(str(current_record.get("current_review_input_file", "") or "").strip())
    )
    lines = [
        f"# Operator Prompt for {task_id}",
        "",
        (
            "You are Codex's independent read-only semantic reviewer for exactly one Lean task in this repository."
            if review_mode_active
            else "You are Codex's local authoring agent for exactly one Lean task in this repository."
        ),
        "",
        "Rules:",
        *(
            [
                "1. Return semantic review JSON only.",
                "2. Read `semantic_review_input.json`, `semantic_review_prompt.md`, `semantic_review_context.md`, and `semantic_review_result_template.json` before writing the result.",
                "3. Write the verdict into the exact `semantic_review_result_vM.json` path requested by the current review request.",
                "4. Keep the binding fields unchanged; do not review a different candidate or invent a different task binding.",
                "5. Judge semantic fidelity, proof spine, interface contract, and downstream adequacy; do not edit `draft.lean` in reviewer mode.",
                "6. You must be independent from the authoring pass for this candidate. Fill `reviewer_independence` truthfully.",
                "7. If you authored or edited this candidate, stop and hand the review to a different read-only reviewer subagent or configured reviewer runner.",
            ]
            if review_mode_active
            else [
                "1. Return Lean code only.",
                "2. Edit `draft.lean` as the working file. Do not treat `target_stub.lean` as the final output.",
                "3. Reuse the imports listed in `imports.lean`.",
                "4. Prefer only `verified` entries from `search_manifest.json` when choosing names, imports, and APIs.",
                "5. Read `failure_summary.md` before the next attempt and avoid repeating the same failure mode.",
                "6. Do not redefine any object already provided by Mathlib or uploaded local dependencies.",
                "7. Do not rewrite dependency files.",
                "8. Produce complete Lean code with no `sorry`.",
                "9. Run `build-check` after each meaningful edit loop; do not enter semantic review until the candidate is build-ready.",
                "10. Preserve the original TeX statement faithfully; use `review-now --review-subject candidate` after `build-check` passes.",
                "11. Use `review-now --review-subject existing` only for auditing an already runnable official output.",
                "12. Use `verify` only when a stable external reviewer runner is configured.",
            ]
        ),
    ]
    if ledger is not None and pack_dir is not None:
        route_note = _official_output_route_note(
            task,
            current_record if isinstance(current_record, dict) else {},
            settings,
            pack_dir,
        ) if settings is not None else ""
        if route_note:
            lines.extend(["", "Official output routing guard:", f"- {route_note}"])
        repair_request_file = str(current_record.get("current_review_repair_request_file", "") or "").strip()
        if auto_loop_state["enabled"]:
            lines.extend(
                [
                    "",
                    "## Active Auto-Loop",
                    "",
                    f"- Status: `{auto_loop_state['status'] or '(unknown)'}`",
                    f"- Entry subject: `{auto_loop_state['entry_subject'] or '(unknown)'}`",
                    f"- Round: `{auto_loop_state['round']}`",
                    f"- Phase: `{auto_loop_state['phase'] or '(none)'}`",
                    f"- Consecutive non-progress count: `{auto_loop_state['consecutive_nonprogress']}`",
                ]
            )
            if auto_loop_state["stop_reason"]:
                lines.append(f"- Stop reason: `{auto_loop_state['stop_reason']}`")
                stop_note = _auto_loop_stop_reason_note(auto_loop_state["stop_reason"])
                if stop_note:
                    lines.append(f"- Stop reason note: {stop_note}")
            next_action = _auto_loop_next_action(current_record)
            if next_action:
                lines.append(f"- Next action: `{next_action}`")
            if review_mode_active:
                lines.extend(
                    [
                        "",
                        "Current same-session action:",
                        "- You are in independent read-only semantic review mode for the current auto-loop round.",
                        "- Read the current semantic review request artifacts.",
                        "- Write the canonical `semantic_review_result` JSON for the current candidate, including `reviewer_independence`.",
                        "- Immediately rerun `auto-loop` after writing the canonical review result so runtime can apply it or start the next repair/build round.",
                        "- Do not wait for a new user message to continue the current auto-loop.",
                        "- The orchestrator may hand this review to a distinct reviewer subagent or configured reviewer runner; the author must not self-review.",
                    ]
                )
            else:
                lines.extend(
                    [
                        "",
                        "Current same-session action:",
                        "- Continue authoring in `draft.lean` until `build-check` succeeds.",
                        "- Immediately rerun `auto-loop` after each meaningful authoring pass or build result; do not stop at a build failure.",
                        "- Do not wait for a new user message to continue the current auto-loop.",
                        "- The runtime will then prepare or apply the next review/repair step in this same Codex session.",
                    ]
                )
        if repair_request_file:
            repair_request_path = Path(repair_request_file).expanduser()
            if not repair_request_path.is_absolute():
                repair_request_path = (pack_dir / repair_request_path).resolve()
            repair_request = read_json_safely(repair_request_path, {})
            if isinstance(repair_request, dict):
                lines.extend(
                    [
                        "",
                        "## Active Semantic Repair",
                        "",
                        "You are in semantic repair mode. The current goal is to remove the semantic defect identified by the failed review, not merely to make the file compile.",
                        "Treat `review_repair_request.json` and the canonical failed review artifacts as the primary repair inputs.",
                        "`failure_summary.md` and current build diagnostics remain useful, but they are secondary to the semantic defect contract.",
                        "Do not answer the failed review with a syntax-only patch if the semantic mismatch would remain.",
                        "",
                        "Current repair targets:",
                    ]
                )
                for item in repair_request.get("must_fix", []):
                    lines.append(f"- Must fix: {item}")
                for item in repair_request.get("must_preserve", []):
                    lines.append(f"- Must preserve: {item}")
                for item in repair_request.get("forbidden_shortcuts", []):
                    lines.append(f"- Forbidden shortcut: {item}")
                for item in repair_request.get("downstream_blockers", []):
                    lines.append(f"- Downstream blocker: {item}")
    lines.extend(
        [
            "",
            "Inputs in this pack:",
            "- `context.md`: task statement, dependency summary, current repo constraints",
            "- `intent_contract.json`: legacy heuristic notes; do not treat it as the semantic source of truth",
            "- `search_manifest.json`: structured verified/rejected grounding evidence",
            "- `search_notes.md`: human-readable deterministic Mathlib/local search results and `#check` outputs",
            "- `failure_summary.md`: latest build summary and next-step guidance",
            "- `imports.lean`: required imports",
            "- `target_stub.lean`: the baseline output shape",
            "- `draft.lean`: the current editable working file",
            "- `build_result_v*.json` / `build_feedback.txt`: technical build loop outputs",
            "- `semantic_review_*.json/md`: reviewer artifacts written by `review-pack`/`review-existing`/`review-apply` or runner-backed `verify`/`audit`",
            "- `semantic_review_context*.md`: the full review context that reviewers must treat as binding for interface/downstream adequacy",
            "- `review_repair_request*.json` / `review_repair_summary*.md`: repair-loop artifacts derived from failed semantic review cycles",
        ]
    )
    return "\n".join(lines)


def build_context_markdown(task: dict[str, Any], ledger: LedgerManager, settings, pack_dir: Path) -> str:
    task_id = task["block_id"]
    chapter = extract_chapter(task_id)
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    final_union = canonicalize_id_list(hard_deps + soft_imports)
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    pack_candidate_state = str(current_record.get("pack_candidate_state", "draft") or "draft")
    attempt_history = load_attempt_history(pack_dir, task_id)
    build_attempts = [
        item for item in attempt_history.get("attempts", [])
        if isinstance(item, dict) and str(item.get("stage", "legacy_verify")) in {"build", "legacy_verify"}
    ]
    latest_attempt = build_attempts[-1] if build_attempts else None
    failure_summary_text = read_file_safely(pack_dir / FAILURE_SUMMARY_FILE_NAME).strip()
    intent_contract = build_legacy_intent_contract(task)
    latest_operation_file = str(current_record.get("latest_operation_file", "") or "")
    latest_operation_kind = str(current_record.get("latest_operation_kind", "") or "")
    latest_build_result_file = str(current_record.get("latest_build_result_file", "") or "")
    latest_build_result = read_json_safely(Path(latest_build_result_file), {}) if latest_build_result_file else {}
    current_review_input_file = str(current_record.get("current_review_input_file", "") or "")
    current_review_prompt_file = str(current_record.get("current_review_prompt_file", "") or "")
    current_review_template_file = str(current_record.get("current_review_template_file", "") or "")
    current_review_context_file = str(current_record.get("current_review_context_file", "") or "")
    current_review_request_file = str(current_record.get("current_review_request_file", "") or "")
    current_review_backend_id = str(current_record.get("current_review_backend_id", "") or "")
    current_review_expected_result_file = str(current_record.get("current_review_expected_result_file", "") or "")
    current_review_subject_kind = str(current_record.get("current_review_subject_kind", "") or "")
    current_review_origin = str(current_record.get("current_review_origin", "") or "")
    current_review_repair_request_file = str(current_record.get("current_review_repair_request_file", "") or "")
    current_review_repair_summary_file = str(current_record.get("current_review_repair_summary_file", "") or "")
    current_review_repair_seed_file = str(current_record.get("current_review_repair_seed_file", "") or "")
    current_review_repair_origin_result_file = str(current_record.get("current_review_repair_origin_result_file", "") or "")
    current_review_repair_archive_file = str(current_record.get("current_review_repair_archive_file", "") or "")
    latest_review_result_file = str(current_record.get("latest_semantic_review_result_file", "") or "")
    latest_review_result = read_json_safely(Path(latest_review_result_file), {}) if latest_review_result_file else {}
    current_repair_request_path = Path(current_review_repair_request_file).expanduser() if current_review_repair_request_file else None
    if current_repair_request_path is not None and not current_repair_request_path.is_absolute():
        current_repair_request_path = (pack_dir / current_repair_request_path).resolve()
    current_repair_request = read_json_safely(current_repair_request_path, {}) if current_repair_request_path else {}
    official_route_note = _official_output_route_note(
        task,
        current_record if isinstance(current_record, dict) else {},
        settings,
        pack_dir,
    )
    stale_ready = (
        str(current_record.get("latest_build_ready_candidate_kind", "") or "") == ""
        and str(current_record.get("latest_build_candidate_kind", "") or "") == "draft"
        and str(current_record.get("pack_candidate_state", "") or "") == "draft"
        and bool(str(current_record.get("latest_build_candidate_file", "") or ""))
    )
    lines = [
        f"# Context for {task_id}",
        "",
        f"- Type: `{task.get('type', 'Unknown')}`",
        f"- Source plan: `{task.get('source_plan', 'unknown')}`",
        f"- Chapter: `{chapter}`" if chapter is not None else "- Chapter: unknown",
        f"- Current ledger status: `{current_record.get('status', 'UNKNOWN')}`",
        f"- Pack candidate state: `{pack_candidate_state}`",
        "",
        "## Task",
        "",
        f"### Title\n{task.get('title', '').strip() or '(untitled)'}",
        "",
        "### Content",
        "",
        task.get("content", "").strip() or "(no content)",
        "",
        "## Legacy Heuristic Notes",
        "",
        "These notes are advisory only. Hard checks and reviewer artifacts are the promotion gates.",
        "",
        f"- Task role: `{intent_contract.get('task_role', 'unknown')}`",
        f"- Coverage mode: `{intent_contract.get('coverage_mode', 'strict_source_alignment')}`",
        f"- Required cues: `{', '.join(intent_contract.get('required_cues', [])) or '(none)'}`",
        f"- Forbidden relaxations: `{', '.join(intent_contract.get('forbidden_relaxations', [])) or '(none)'}`",
        f"- Must not assume: `{', '.join(intent_contract.get('must_not_assume', [])) or '(none)'}`",
        "",
        "Rules for this task:",
        "- Examples must preserve the source construction, counterexample logic, density/distribution assumptions, and conclusion; do not reduce them to a theorem wrapper.",
        "- Theorems must not strengthen hypotheses to erase the main textbook argument.",
        "",
        "## Hard Dependencies",
        "",
    ]

    if not hard_deps:
        lines.append("- None")
    else:
        for dep in hard_deps:
            dep_id = canonicalize_block_id(dep)
            dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
            dep_file = find_existing_task_file(dep_id, dep_record.get("source_plan", "unknown"), settings)
            dep_code = read_file_safely(dep_file) if dep_file else ""
            lines.append(f"### `{dep_id}`")
            lines.append(f"- Status: `{dep_record.get('status', 'UNKNOWN')}`")
            exported = dep_record.get("exported_symbols", [])
            lines.append(f"- Exported symbols: `{', '.join(exported) if exported else '(none recorded)'}`")
            lines.append(f"- File: `{dep_file}`" if dep_file else "- File: `(not found)`")
            if dep_code:
                lines.extend(["", "```lean", dep_code[:1200].strip(), "```", ""])
            else:
                lines.append("")

    lines.extend(["## Soft Imports", ""])
    if not soft_imports:
        lines.append("- None")
    else:
        for dep in soft_imports:
            dep_id = canonicalize_block_id(dep)
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

    lines.extend(["", "## Latest Operation Summary", ""])
    lines.append(f"- Latest operation kind: `{latest_operation_kind or '(none)'}`")
    lines.append(f"- Latest operation file: `{latest_operation_file or '(none)'}`")

    lines.extend(["", "## Build State", ""])
    lines.append(f"- Build attempts recorded: `{len(build_attempts)}`")
    lines.append(f"- Latest build candidate: `{current_record.get('latest_build_candidate_file', '') or '(none)'}`")
    lines.append(f"- Latest build-ready candidate: `{current_record.get('latest_build_ready_candidate_file', '') or '(none)'}`")
    lines.append(f"- Latest build result: `{latest_build_result_file or '(none)'}`")
    if stale_ready:
        lines.append("- last build-ready candidate is stale")
    if official_route_note:
        lines.append(f"- Official output routing guard: {official_route_note}")
    if latest_attempt:
        lines.append(f"- Latest build status: `{'success' if latest_attempt.get('success') else 'failure'}`")
        lines.append(f"- Latest primary failure kind: `{latest_attempt.get('primary_failure_kind', 'none')}`")
        blocking = latest_attempt.get("blocking_symbols", [])
        if isinstance(blocking, list) and blocking:
            lines.append(f"- Latest blocking symbols: `{', '.join(blocking)}`")
    else:
        lines.append("- Latest build status: `(no build checks yet)`")
    if isinstance(latest_build_result, dict) and latest_build_result:
        lines.append(f"- Latest build disposition: `{latest_build_result.get('disposition', '') or '(none)'}`")

    lines.extend(["", "## Review State", ""])
    if current_review_input_file:
        if pack_candidate_state == "review_pending":
            lines.append("- Current review status: `awaiting reviewer result for the current review pack`")
        else:
            origin_label = current_review_origin or "prepared reviewer materials"
            lines.append(f"- Current review status: `review materials prepared via {origin_label}`")
        lines.append(f"- Current review origin: `{current_review_origin or '(unknown)'}`")
        lines.append(f"- Current review subject kind: `{current_review_subject_kind or '(unknown)'}`")
        lines.append(f"- Current review input: `{current_review_input_file}`")
        lines.append(f"- Current review prompt: `{current_review_prompt_file or '(none)'}`")
        lines.append(f"- Current review context: `{current_review_context_file or '(none)'}`")
        lines.append(f"- Current review template: `{current_review_template_file or '(none)'}`")
        lines.append(f"- Current review request: `{current_review_request_file or '(none)'}`")
        lines.append(f"- Current review request backend: `{current_review_backend_id or '(none)'}`")
        lines.append(f"- Current expected review result file: `{current_review_expected_result_file or '(none)'}`")
        if latest_review_result_file:
            lines.append("- The completed review result below is from the previous review cycle, not the current pending pack.")
        lines.append("")
    lines.append(f"- Last completed semantic review result: `{latest_review_result_file or '(none)'}`")
    if isinstance(latest_review_result, dict) and latest_review_result:
        lines.append(f"- Last completed semantic verdict: `{latest_review_result.get('verdict', 'inconclusive')}`")
        lines.append(f"- Last completed semantic summary: `{latest_review_result.get('summary', '') or '(none)'}`")
    else:
        lines.append("- Last completed semantic verdict: `(no completed review result yet)`")

    auto_loop_state = auto_loop_state_from_record(current_record if isinstance(current_record, dict) else {})
    lines.extend(["", "## Auto-Loop State", ""])
    if auto_loop_state["enabled"]:
        lines.append(f"- Current auto-loop status: `{auto_loop_state['status'] or '(unknown)'}`")
        lines.append(f"- Current auto-loop entry subject: `{auto_loop_state['entry_subject'] or '(unknown)'}`")
        lines.append(f"- Current auto-loop round: `{auto_loop_state['round']}`")
        lines.append(f"- Current auto-loop phase: `{auto_loop_state['phase'] or '(none)'}`")
        next_action = _auto_loop_next_action(current_record)
        if next_action:
            lines.append(f"- Current auto-loop next action: `{next_action}`")
        lines.append(f"- Current auto-loop max rounds: `{auto_loop_state['max_rounds']}`")
        lines.append(
            f"- Current auto-loop max build attempts per round: `{auto_loop_state['max_build_attempts_per_round']}`"
        )
        lines.append(f"- Current auto-loop non-progress limit: `{auto_loop_state['nonprogress_limit']}`")
        lines.append(
            f"- Current auto-loop consecutive non-progress count: `{auto_loop_state['consecutive_nonprogress']}`"
        )
        if auto_loop_state["stop_reason"]:
            lines.append(f"- Current auto-loop stop reason: `{auto_loop_state['stop_reason']}`")
            stop_note = _auto_loop_stop_reason_note(auto_loop_state["stop_reason"])
            if stop_note:
                lines.append(f"- Current auto-loop stop note: {stop_note}")
    else:
        lines.append("- Current auto-loop status: `(inactive)`")

    lines.extend(["", "## Active Repair State", ""])
    if current_review_repair_request_file:
        lines.append("- Active repair status: `ready for semantic repair / build loop`")
        lines.append(f"- Active repair request: `{current_review_repair_request_file}`")
        lines.append(f"- Active repair summary: `{current_review_repair_summary_file or '(none)'}`")
        lines.append(f"- Repair seed file: `{current_review_repair_seed_file or '(none)'}`")
        lines.append(f"- Failed review result: `{current_review_repair_origin_result_file or '(none)'}`")
        if current_review_repair_archive_file:
            lines.append(f"- Archived pre-repair draft: `{current_review_repair_archive_file}`")
        if isinstance(current_repair_request, dict) and current_repair_request:
            must_fix = current_repair_request.get("must_fix", [])
            blockers = current_repair_request.get("downstream_blockers", [])
            if isinstance(must_fix, list) and must_fix:
                lines.append(f"- Must-fix summary: `{must_fix[0]}`")
            if isinstance(blockers, list) and blockers:
                lines.append(f"- Downstream blockers: `{'; '.join(str(item) for item in blockers if str(item).strip())}`")
    else:
        lines.append("- Active repair status: `(none)`")

    lines.extend(["", "## Compatibility State", ""])
    lines.append(f"- Latest verify summary: `{current_record.get('latest_verify_result_file', '') or '(none)'}`")

    if current_record.get("last_error"):
        lines.extend(["", "## Recent Failure Feedback", "", "```text", current_record["last_error"], "```", ""])
    if failure_summary_text:
        lines.extend(["## Failure Summary", "", failure_summary_text, ""])

    return "\n".join(lines).rstrip() + "\n"


def _dependency_review_metadata(
    dep_id: str,
    dep_record: dict[str, Any] | None,
    settings,
) -> dict[str, Any]:
    dep_id = canonicalize_block_id(dep_id)
    record = dep_record if isinstance(dep_record, dict) else {}
    source_plan = str(record.get("source_plan", "unknown") or "unknown")
    dep_file = find_existing_task_file(dep_id, source_plan, settings)
    exported_symbols = record.get("exported_symbols", [])
    if not isinstance(exported_symbols, list):
        exported_symbols = []

    if record:
        return {
            "title": str(record.get("title", "") or "(untitled)"),
            "status": str(record.get("status", "UNKNOWN") or "UNKNOWN"),
            "source_plan": source_plan,
            "file": str(dep_file or ""),
            "exported_symbols": exported_symbols,
            "ledger_missing": False,
        }

    inferred_source_plan = source_plan
    inferred_exports: list[str] = []
    if dep_file:
        dep_code = read_file_safely(dep_file)
        source_match = re.search(r"(?m)^\s*SOURCE PLAN:\s*(?P<source>.+?)\s*$", dep_code)
        if source_match:
            inferred_source_plan = source_match.group("source").strip() or source_plan
        for match in re.finditer(
            r"(?m)^\s*(?:noncomputable\s+)?(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)\b",
            dep_code,
        ):
            inferred_exports.append(match.group(1))
            if len(inferred_exports) >= 8:
                break

    return {
        "title": "(ledger entry missing; output file present)" if dep_file else "(untitled)",
        "status": "OUTPUT_PRESENT_LEDGER_MISSING" if dep_file else "UNKNOWN",
        "source_plan": inferred_source_plan,
        "file": str(dep_file or ""),
        "exported_symbols": inferred_exports,
        "ledger_missing": not bool(record),
    }


def build_semantic_review_context_markdown(task: dict[str, Any], ledger: LedgerManager, settings, pack_dir: Path) -> str:
    task_id = task["block_id"]
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    source_plan = str(task.get("source_plan", "unknown") or "unknown")
    downstream = _collect_direct_downstream_consumers(task_id, settings)
    hard_deps = canonicalize_id_list(task.get("dependencies", []))
    soft_imports = canonicalize_id_list(task.get("soft_imports", []))
    active_targets = list(iter_official_output_targets(task_id, source_plan, settings))
    public_exports = current_record.get("exported_symbols", [])
    if not isinstance(public_exports, list):
        public_exports = []
    lines = [
        f"# Semantic Review Context for {task_id}",
        "",
        "This file is the authoritative review context for `review-pack` and `review-existing`.",
        "A local build is not enough: the reviewer must check statement fidelity, proof spine adequacy, interface contract, and downstream adequacy against this context.",
        "",
        "## Original Task Text",
        "",
        f"- Type: `{task.get('type', '')}`",
        f"- Source plan: `{source_plan}`",
        f"- Title: `{str(task.get('title', '') or '(untitled)').strip()}`",
        "",
        str(task.get("content", "") or "(no content)").strip(),
        "",
        "## Upstream Textbook Chain",
        "",
    ]
    if not hard_deps and not soft_imports:
        lines.append("- No declared upstream textbook tasks.")
    else:
        for relation_name, deps in (("Hard dependencies", hard_deps), ("Soft imports", soft_imports)):
            lines.append(f"### {relation_name}")
            if not deps:
                lines.append("- None")
                continue
            for dep in deps:
                dep_id = canonicalize_block_id(dep)
                dep_record = ledger.ledger.get("tasks", {}).get(dep_id, {})
                dep_meta = _dependency_review_metadata(dep_id, dep_record, settings)
                lines.append(
                    f"- `{dep_id}` from `{dep_meta['source_plan']}` / `{dep_meta['status']}`: {dep_meta['title']}"
                )
                if dep_meta["ledger_missing"] and dep_meta["file"]:
                    lines.append(f"  - Fallback output file: `{dep_meta['file']}`")
                if dep_meta["ledger_missing"] and dep_meta["exported_symbols"]:
                    lines.append(
                        f"  - Fallback declarations: `{', '.join(str(item) for item in dep_meta['exported_symbols'])}`"
                    )
    lines.extend(["", "## Direct Downstream Consumers", ""])
    if not downstream:
        lines.append("- No direct downstream consumers were found in current plans.")
    else:
        for consumer in downstream:
            lines.append(
                f"- `{consumer['block_id']}` from `{consumer['source_plan']}` via `{consumer['relation']}` / `{consumer['type']}`: {consumer['title'] or '(untitled)'}"
            )
    lines.extend(["", "## Current Public Interface Summary", ""])
    lines.append(f"- Official output targets: `{', '.join(str(path) for path in active_targets) if active_targets else '(none)'}`")
    lines.append(f"- Recorded exported symbols: `{', '.join(str(item) for item in public_exports) if public_exports else '(none recorded)'}`")
    lines.append(f"- Current ledger status: `{current_record.get('status', 'UNKNOWN')}`")
    lines.append(f"- Build candidate state: `{current_record.get('pack_candidate_state', 'draft')}`")
    latest_review_result = str(current_record.get("latest_semantic_review_result_file", "") or "")
    lines.append(f"- Last completed semantic review result: `{latest_review_result or '(none)'}`")
    spine_contract = review_spine_contract(task)
    lines.extend(["", "## General Source Spine Review Contract", ""])
    lines.append(f"- Required for pass: `{spine_contract['required_for_pass']}`")
    lines.append(f"- Rule: {spine_contract['general_rule']}")
    lines.append("- Acceptable abstraction:")
    for item in spine_contract["acceptable_abstraction"]:
        lines.append(f"  - {item}")
    lines.append("- Automatic fail patterns:")
    for item in spine_contract["automatic_fail_patterns"]:
        lines.append(f"  - {item}")
    lines.append("- Pass evidence requirements:")
    for item in spine_contract["pass_evidence_requirements"]:
        lines.append(f"  - {item}")
    proof_obligations = maybe_ensure_proof_obligations_file(
        pack_dir,
        task,
        current_record=current_record if isinstance(current_record, dict) else {},
        tracking_level=2,
    )
    if proof_obligations is None:
        lines.extend(
            [
                "",
                "## Proof Obligation Tracking",
                "",
                "- Proof obligation tracking: `Level 0 ordinary Phase2 path`.",
                "- No task-local `proof_obligations.json` is generated for this normal task.",
            ]
        )
    else:
        lines.extend(["", render_proof_obligations_markdown(proof_obligations, path=pack_dir / PROOF_OBLIGATIONS_FILE_NAME).rstrip()])
    lines.extend(["", "## Allowed Abstraction Layer", ""])
    for item in review_allowed_abstractions(task):
        lines.append(f"- {item}")
    lines.extend(["", "## Forbidden Weakenings", ""])
    for item in review_forbidden_weakenings(task):
        lines.append(f"- {item}")
    lines.extend(["", "## Historical Shortcut / Shell Risks", ""])
    risks = review_history_risks(task_id)
    if risks:
        for item in risks:
            lines.append(f"- {item}")
    else:
        lines.append("- No task-specific historical shortcut is recorded; still enforce the general forbidden weakenings above.")
    lines.extend(["", "## Downstream Acceptance Checklist", ""])
    checklist = review_downstream_checklist(task_id)
    if checklist:
        for item in checklist:
            lines.append(f"- {item}")
    else:
        lines.append("- No extra downstream checklist recorded beyond the general rubric.")
    lines.extend(["", "## Pack Snapshot", ""])
    lines.append(f"- Pack directory: `{pack_dir}`")
    lines.append(f"- Context markdown: `{pack_dir / 'context.md'}`")
    lines.append(f"- Search manifest: `{pack_dir / SEARCH_MANIFEST_FILE_NAME}`")
    lines.append(f"- Intent contract: `{intent_contract_path(pack_dir)}`")
    return "\n".join(lines).rstrip() + "\n"


def _render_review_repair_summary(
    repair_request: dict[str, Any],
    *,
    warning_lines: list[str] | None = None,
    archive_file: str = "",
) -> str:
    warning_lines = [item for item in (warning_lines or []) if str(item).strip()]
    lines = [
        f"# Review Repair Summary for {repair_request.get('task_id', '')}",
        "",
        f"- Failed verdict: `{repair_request.get('failed_verdict', 'inconclusive')}`",
        f"- Origin review mode: `{repair_request.get('origin_review_mode', '')}`",
        f"- Failed review input: `{repair_request.get('failed_review_input_file', '')}`",
        f"- Failed review result: `{repair_request.get('failed_review_result_file', '')}`",
        f"- Failed review report: `{repair_request.get('failed_review_report_file', '')}`",
        f"- Failed review subject: `{repair_request.get('failed_review_subject_file', '')}`",
        f"- Next draft seed: `{repair_request.get('next_draft_seed_file', '')}`",
    ]
    if archive_file:
        lines.append(f"- Archived prior draft: `{archive_file}`")
    if warning_lines:
        lines.extend(["", "## Warnings", ""])
        for item in warning_lines:
            lines.append(f"- {item}")
    lines.extend(["", "## Must Fix", ""])
    for item in repair_request.get("must_fix", []):
        lines.append(f"- {item}")
    lines.extend(["", "## Must Preserve", ""])
    for item in repair_request.get("must_preserve", []):
        lines.append(f"- {item}")
    forbidden_shortcuts = repair_request.get("forbidden_shortcuts", [])
    if forbidden_shortcuts:
        lines.extend(["", "## Forbidden Shortcuts", ""])
        for item in forbidden_shortcuts:
            lines.append(f"- {item}")
    proof_obligation_blockers = repair_request.get("proof_obligation_blockers", [])
    if proof_obligation_blockers:
        lines.extend(["", "## Proof Obligation Blockers", ""])
        for item in proof_obligation_blockers:
            if isinstance(item, dict):
                lines.append(f"- `{item.get('obligation_id', '') or '(unassigned)'}`: {item.get('issue', '')}")
            else:
                lines.append(f"- {item}")
    downstream_blockers = repair_request.get("downstream_blockers", [])
    if downstream_blockers:
        lines.extend(["", "## Downstream Blockers", ""])
        for item in downstream_blockers:
            lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Next Step",
            "",
            "- Edit `draft.lean` from the seeded file, remove the semantic defect, then rerun `build-check`.",
            "- Do not answer this repair cycle with a syntax-only patch if the semantic mismatch would remain.",
        ]
    )
    return "\n".join(lines).rstrip() + "\n"


def build_failure_summary_markdown(
    task_id: str,
    history: dict[str, Any],
    auto_loop_state: dict[str, Any] | None = None,
) -> str:
    current_auto_loop = auto_loop_state or {}
    all_attempts = [item for item in history.get("attempts", []) if isinstance(item, dict)]
    latest_overall = all_attempts[-1] if all_attempts else None
    if isinstance(latest_overall, dict) and str(latest_overall.get("stage", "")) == "semantic_review":
        semantic_attempts = [item for item in all_attempts if str(item.get("stage", "")) == "semantic_review"]
        build_attempts = [item for item in all_attempts if str(item.get("stage", "legacy_verify")) in {"build", "legacy_verify"}]
        lines = [
            f"# Failure Summary for {task_id}",
            "",
            f"- Total runtime attempts: `{len(all_attempts)}`",
            f"- Total build attempts: `{len(build_attempts)}`",
            f"- Total semantic review outcomes: `{len(semantic_attempts)}`",
            f"- Latest candidate: `{latest_overall.get('candidate_file', '(unknown)')}`",
            f"- Latest semantic review verdict: `{latest_overall.get('review_verdict', 'unknown')}`",
            f"- Latest disposition: `{latest_overall.get('disposition', 'unknown')}`",
        ]
        if current_auto_loop.get("enabled"):
            lines.extend(
                [
                    f"- Latest auto-loop status: `{current_auto_loop.get('status', '(unknown)') or '(unknown)'}`",
                    f"- Latest auto-loop round: `{current_auto_loop.get('round', 0)}`",
                    f"- Latest auto-loop phase: `{current_auto_loop.get('phase', '(none)') or '(none)'}`",
                    f"- Latest auto-loop non-progress count: `{current_auto_loop.get('consecutive_nonprogress', 0)}`",
                ]
            )
            next_action = _auto_loop_next_action(current_auto_loop)
            if next_action:
                lines.append(f"- Latest auto-loop next action: `{next_action}`")
            stop_reason = str(current_auto_loop.get("stop_reason", "") or "").strip()
            if stop_reason:
                lines.append(f"- Latest auto-loop stop reason: `{stop_reason}`")
                stop_note = _auto_loop_stop_reason_note(stop_reason)
                if stop_note:
                    lines.append(f"- Latest auto-loop stop note: {stop_note}")
        review_summary = str(latest_overall.get("review_summary", "") or "").strip()
        if review_summary:
            lines.append(f"- Latest semantic summary: `{review_summary}`")
        repair_request_file = str(latest_overall.get("repair_request_file", "") or "").strip()
        if repair_request_file:
            lines.append(f"- Active repair request: `{repair_request_file}`")
        lines.extend(["", "## Recent Attempts", ""])
        for attempt in all_attempts[-5:]:
            stage = str(attempt.get("stage", "legacy_verify") or "legacy_verify")
            if stage == "semantic_review":
                lines.append(f"- Attempt `{attempt.get('attempt', '?')}`: `semantic_review` / `{attempt.get('review_verdict', 'unknown')}` / `{attempt.get('disposition', 'unknown')}` / `{attempt.get('candidate_file', '(unknown)')}`")
            else:
                lines.append(f"- Attempt `{attempt.get('attempt', '?')}`: `{'success' if attempt.get('success') else 'failure'}` / `{attempt.get('primary_failure_kind', 'none')}` / `{attempt.get('candidate_file', '(unknown)')}`")
        lines.extend(["", "## Recommended Next Action", ""])
        primary_failure_kind = str(latest_overall.get("primary_failure_kind", "") or "")
        if latest_overall.get("success"):
            lines.append("- The latest semantic review passed and the candidate was promoted. If `draft.lean` changes again, rerun `build-check` before any new review.")
        elif primary_failure_kind == "semantic_review_invalid":
            lines.append("- The latest semantic review artifact was stale or invalid. Regenerate a fresh request with `review-now` before applying another review result.")
        else:
            lines.append("- Read `review_repair_request.json` and the failed semantic review artifacts, run `review-fix`, then return to the repair-mode `build-check` loop.")
        return "\n".join(lines).rstrip() + "\n"

    attempts = [item for item in history.get("attempts", []) if isinstance(item, dict) and str(item.get("stage", "legacy_verify")) in {"build", "legacy_verify"}]
    lines = [f"# Failure Summary for {task_id}", ""]
    if not attempts:
        lines.extend(
            [
                "No build-check attempts have been recorded yet.",
                "",
                "Recommended next action:",
                "- Read `search_manifest.json`, then edit `draft.lean` and run `build-check`.",
                "- Once `build-check` succeeds, run `review-now --review-subject candidate`.",
                "- Use `verify` only if `TOY_APOLLO_PHASE2_REVIEWER_ARGV_JSON` points to a stable local reviewer runner.",
            ]
        )
        if current_auto_loop.get("enabled"):
            lines.extend(["", "## Auto-Loop State", "", f"- Latest auto-loop status: `{current_auto_loop.get('status', '(unknown)') or '(unknown)'}`", f"- Latest auto-loop round: `{current_auto_loop.get('round', 0)}`", f"- Latest auto-loop phase: `{current_auto_loop.get('phase', '(none)') or '(none)'}`", f"- Latest auto-loop non-progress count: `{current_auto_loop.get('consecutive_nonprogress', 0)}`"])
            next_action = _auto_loop_next_action(current_auto_loop)
            if next_action:
                lines.append(f"- Latest auto-loop next action: `{next_action}`")
            stop_reason = str(current_auto_loop.get("stop_reason", "") or "").strip()
            if stop_reason:
                lines.append(f"- Latest auto-loop stop reason: `{stop_reason}`")
                stop_note = _auto_loop_stop_reason_note(stop_reason)
                if stop_note:
                    lines.append(f"- Latest auto-loop stop note: {stop_note}")
        return "\n".join(lines).rstrip() + "\n"

    latest = attempts[-1]
    _, repeated_count = count_consecutive_primary_failures(attempts)
    recent_attempts = attempts[-5:]
    primary_kinds = [str(item.get("primary_failure_kind") or "") for item in attempts if str(item.get("primary_failure_kind") or "")]
    counts = Counter(primary_kinds)
    lines.extend([f"- Total build attempts: `{len(attempts)}`", f"- Latest candidate: `{latest.get('candidate_file', '(unknown)')}`", f"- Latest result: `{'success' if latest.get('success') else 'failure'}`", f"- Latest primary failure kind: `{latest.get('primary_failure_kind', 'none')}`"])
    if current_auto_loop.get("enabled"):
        lines.extend([f"- Latest auto-loop status: `{current_auto_loop.get('status', '(unknown)') or '(unknown)'}`", f"- Latest auto-loop round: `{current_auto_loop.get('round', 0)}`", f"- Latest auto-loop phase: `{current_auto_loop.get('phase', '(none)') or '(none)'}`", f"- Latest auto-loop non-progress count: `{current_auto_loop.get('consecutive_nonprogress', 0)}`"])
        next_action = _auto_loop_next_action(current_auto_loop)
        if next_action:
            lines.append(f"- Latest auto-loop next action: `{next_action}`")
        stop_reason = str(current_auto_loop.get("stop_reason", "") or "").strip()
        if stop_reason:
            lines.append(f"- Latest auto-loop stop reason: `{stop_reason}`")
            stop_note = _auto_loop_stop_reason_note(stop_reason)
            if stop_note:
                lines.append(f"- Latest auto-loop stop note: {stop_note}")
    blocking = latest.get("blocking_symbols", [])
    if isinstance(blocking, list) and blocking:
        lines.append(f"- Latest blocking symbols: `{', '.join(blocking)}`")
    lines.extend(["", "## Recent Attempts", ""])
    for attempt in recent_attempts:
        lines.append(f"- Attempt `{attempt.get('attempt', '?')}`: `{'success' if attempt.get('success') else 'failure'}` / `{attempt.get('primary_failure_kind', 'none')}` / `{attempt.get('candidate_file', '(unknown)')}`")
    repeated = [f"{kind} x{count}" for kind, count in counts.items() if count >= 2]
    lines.extend(["", "## Repeated Failure Patterns", ""])
    if repeated:
        for item in repeated:
            lines.append(f"- `{item}`")
    else:
        lines.append("- No repeated failure pattern yet.")
    lines.extend(["", "## Recommended Next Action", ""])
    if latest.get("success"):
        lines.append("- The latest candidate passed verification/build checks. Keep `draft.lean` aligned with that snapshot and run `review-now --review-subject candidate` next.")
    else:
        lines.append(f"- {recommended_action_for_kind(str(latest.get('primary_failure_kind') or ''), repeated_count)}")
    return "\n".join(lines).rstrip() + "\n"


def render_semantic_review_report(review_result: dict[str, Any]) -> str:
    return _semantic_review_report(review_result)


def _sync_stale_build_ready_candidate(task_id: str, ledger: LedgerManager, settings, pack_dir: Path) -> bool:
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    if not isinstance(current_record, dict):
        return False
    if str(current_record.get("latest_build_ready_candidate_kind", "") or "") != "draft":
        return False
    ready_hash = str(current_record.get("latest_build_ready_candidate_hash", "") or "")
    if not ready_hash:
        return False
    draft_path = pack_dir / DRAFT_FILE_NAME
    draft_hash = sha256_text(read_file_safely(draft_path)) if draft_path.exists() else ""
    if draft_hash == ready_hash:
        return False

    updates: dict[str, Any] = {
        "latest_build_ready_candidate_kind": "",
        "latest_build_ready_candidate_file": "",
        "latest_build_ready_candidate_hash": "",
    }
    if str(current_record.get("pack_candidate_state", "") or "") in {"build_ready", "review_pending", "review_rejected"}:
        updates["pack_candidate_state"] = "draft"
    ledger.update_runtime_metadata(task_id, **updates)
    return True


def refresh_pack_runtime_view(task: dict[str, Any], ledger: LedgerManager, settings, pack_dir: Path) -> None:
    task_id = task["block_id"]
    _sync_stale_build_ready_candidate(task_id, ledger, settings, pack_dir)
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    latest_review_paths = latest_semantic_review_artifact_paths(pack_dir)
    latest_review_context = latest_semantic_review_context_path(pack_dir)
    latest_review_request = _latest_review_request_path(pack_dir)
    latest_repair_request = list_versioned_json_files(pack_dir, REVIEW_REPAIR_REQUEST_PREFIX)
    latest_repair_summary = list_versioned_md_files(pack_dir, REVIEW_REPAIR_SUMMARY_PREFIX)
    latest_snapshot = select_latest_official_snapshot(pack_dir)
    ledger.update_runtime_metadata(
        task_id,
        latest_semantic_review_input_file=str(latest_review_paths["input"]) if latest_review_paths["input"].exists() else "",
        latest_semantic_review_result_file=str(latest_review_paths["result"]) if latest_review_paths["result"].exists() else "",
        latest_semantic_review_report_file=str(latest_review_paths["report"]) if latest_review_paths["report"].exists() else "",
        latest_semantic_review_context_file=str(latest_review_context) if latest_review_context.exists() else "",
        latest_review_repair_request_file=str(latest_repair_request[-1]) if latest_repair_request else "",
        latest_review_repair_summary_file=str(latest_repair_summary[-1]) if latest_repair_summary else "",
        latest_official_snapshot_file=str(latest_snapshot) if latest_snapshot is not None else str(current_record.get("latest_official_snapshot_file", "") or ""),
        latest_build_result_file=str(current_record.get("latest_build_result_file", "") or select_latest_build_result(pack_dir) or ""),
        latest_verify_result_file=str(current_record.get("latest_verify_result_file", "") or select_latest_verify_result(pack_dir) or ""),
    )
    current_record = ledger.ledger.get("tasks", {}).get(task_id, {})
    metadata_path = pack_dir / "metadata.json"
    metadata = read_json_safely(metadata_path, {})
    if not isinstance(metadata, dict):
        metadata = {}
    metadata["task_id"] = task_id
    metadata["candidate_files"] = [path.name for path in list_candidate_files(pack_dir)]
    metadata["latest_candidate_file"] = str(current_record.get("latest_candidate_file", "") or select_latest_candidate(pack_dir) or "")
    metadata["latest_build_result_file"] = str(current_record.get("latest_build_result_file", "") or select_latest_build_result(pack_dir) or "")
    metadata["latest_verify_result_file"] = str(current_record.get("latest_verify_result_file", "") or select_latest_verify_result(pack_dir) or "")
    metadata["draft_file"] = str(pack_dir / DRAFT_FILE_NAME)
    metadata["intent_contract_file"] = str(intent_contract_path(pack_dir))
    proof_obligations = maybe_ensure_proof_obligations_file(pack_dir, task, current_record=current_record, tracking_level=2)
    metadata["proof_obligations_file"] = str(pack_dir / PROOF_OBLIGATIONS_FILE_NAME) if proof_obligations is not None else ""
    metadata["proof_obligation_summary"] = summarize_proof_obligations(proof_obligations) if proof_obligations is not None else {}
    metadata["search_manifest_file"] = str(pack_dir / SEARCH_MANIFEST_FILE_NAME)
    metadata["attempt_history_file"] = str(pack_dir / ATTEMPT_HISTORY_FILE_NAME)
    metadata["failure_summary_file"] = str(pack_dir / FAILURE_SUMMARY_FILE_NAME)
    metadata["pack_candidate_state"] = str(current_record.get("pack_candidate_state", "draft") or "draft")
    metadata["latest_operation_kind"] = str(current_record.get("latest_operation_kind", "") or "")
    metadata["latest_operation_file"] = str(current_record.get("latest_operation_file", "") or "")
    for field in (
        "latest_build_candidate_kind", "latest_build_candidate_file", "latest_build_candidate_hash",
        "latest_build_ready_candidate_kind", "latest_build_ready_candidate_file", "latest_build_ready_candidate_hash",
        "current_review_input_file", "current_review_prompt_file", "current_review_template_file", "current_review_context_file",
        "current_review_request_file", "current_review_backend_id", "current_review_expected_result_file", "current_review_subject_kind",
        "current_review_subject_file", "current_review_subject_hash", "current_review_origin",
        "latest_semantic_review_input_file", "latest_semantic_review_result_file", "latest_semantic_review_report_file",
        "latest_semantic_review_context_file", "latest_official_snapshot_file", "current_review_repair_request_file",
        "current_review_repair_summary_file", "current_review_repair_seed_file", "current_review_repair_origin_result_file",
        "current_review_repair_archive_file", "latest_review_repair_request_file", "latest_review_repair_summary_file",
        "current_auto_loop_enabled", "current_auto_loop_entry_subject", "current_auto_loop_round", "current_auto_loop_max_rounds",
        "current_auto_loop_max_build_attempts_per_round", "current_auto_loop_nonprogress_limit", "current_auto_loop_consecutive_nonprogress",
        "current_auto_loop_phase", "current_auto_loop_status", "current_auto_loop_stop_reason", "current_auto_loop_last_candidate_hash",
        "current_auto_loop_last_review_fingerprint", "current_auto_loop_last_repair_request_file",
    ):
        metadata[field] = str(current_record.get(field, "") or "")
    for key, path in latest_review_paths.items():
        metadata[f"latest_semantic_review_{key}_file"] = str(path) if path.exists() else ""
    metadata["latest_semantic_review_context_file"] = str(latest_review_context) if latest_review_context.exists() else ""
    metadata["latest_semantic_review_request_file"] = str(latest_review_request) if latest_review_request.exists() else ""
    metadata["latest_review_repair_request_alias_file"] = str(latest_review_repair_request_path(pack_dir)) if latest_review_repair_request_path(pack_dir).exists() else ""
    metadata["latest_review_repair_summary_alias_file"] = str(latest_review_repair_summary_path(pack_dir)) if latest_review_repair_summary_path(pack_dir).exists() else ""
    if latest_snapshot is not None:
        metadata["latest_official_snapshot_file"] = str(latest_snapshot)
    write_json(metadata_path, metadata)
    history = load_attempt_history(pack_dir, task_id)
    auto_loop_state = auto_loop_state_from_record(current_record)
    (pack_dir / FAILURE_SUMMARY_FILE_NAME).write_text(
        build_failure_summary_markdown(task_id, history, auto_loop_state=auto_loop_state),
        encoding="utf-8",
    )
    (pack_dir / "operator_prompt.md").write_text(build_operator_prompt(task, ledger, settings, pack_dir), encoding="utf-8")
    (pack_dir / "context.md").write_text(build_context_markdown(task, ledger, settings, pack_dir), encoding="utf-8")
