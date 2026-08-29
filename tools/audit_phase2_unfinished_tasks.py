from __future__ import annotations

import argparse
import hashlib
import json
import os
import signal
import re
import subprocess
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from src.toy_apollo.state_store import refuse_legacy_ledger_write


TASK_RE = re.compile(r"^(?:def|thm|prob|ex)_(?P<chapter>\d+)(?:_|$)")
REPORT_JSON = "docs/phase2_unfinished_tasks_audit.json"
REPORT_MD = "docs/phase2_unfinished_tasks_audit.md"
CLEAN_DEBT_JSON = "docs/phase2_ch10_14_clean_debt_surface_audit.json"
METADATA_FIX_MANIFEST = "docs/phase2_unfinished_metadata_status_fix_manifest.json"
LEDGER_SUMMARY_SYNC_MANIFEST = "docs/phase2_unfinished_ledger_summary_sync_manifest.json"
ALLOWED_PROOF_BEYOND_BOOK = "thm_14_8_ProofBeyondBook"
ALLOWED_EXCEPTION_TASKS = {"thm_1_2", "ex_1_3_2", "thm_11_8", "thm_14_8"}
SOURCE_STATEMENT_EXCEPTION_TASKS = {"thm_1_2", "ex_1_3_2"}
PASSING_OBLIGATION_STATUSES = {"proved", "obsolete", "accepted_as_proof_debt"}
PLACEHOLDER_OBLIGATION_ID = "source_proof_spine"


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def chapter_for_task_id(task_id: str) -> int | None:
    match = TASK_RE.match(task_id)
    if match is None:
        return None
    return int(match.group("chapter"))


def task_id_in_scope(task_id: str, start_chapter: int, end_chapter: int) -> bool:
    chapter = chapter_for_task_id(task_id)
    return chapter is not None and start_chapter <= chapter <= end_chapter


def output_path(root: Path, task_id: str) -> Path:
    return root / "ToyApollo" / "Output" / f"{task_id}.lean"


def rel(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def is_task_record(task_id: str, task: dict[str, Any]) -> bool:
    if task_id.startswith("obl_"):
        return False
    if chapter_for_task_id(task_id) is None:
        return False
    kind = str(task.get("type", "")).lower()
    return kind not in {"remark", "intro", "proofobligation", "proof_obligation"}


DECL_KIND_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b",
    re.MULTILINE,
)


def declaration_kinds(root: Path) -> dict[str, str]:
    declarations: dict[str, str] = {}
    output_dir = root / "ToyApollo" / "Output"
    if not output_dir.exists():
        return declarations
    for path in sorted(output_dir.glob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for line in text.splitlines():
            match = DECL_KIND_RE.match(line)
            if match:
                declarations[match.group("name")] = match.group("kind")
    return declarations


def theorem_projection_wrappers(root: Path) -> dict[str, str]:
    wrappers: dict[str, str] = {}
    output_dir = root / "ToyApollo" / "Output"
    if not output_dir.exists():
        return wrappers
    for path in sorted(output_dir.glob("*.lean")):
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        matches = list(DECL_KIND_RE.finditer(text))
        for index, match in enumerate(matches):
            if match.group("kind") not in {"theorem", "lemma"}:
                continue
            start = match.start()
            end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
            block = text[start:end]
            if ":=" not in block:
                continue
            body = block.split(":=", 1)[1].strip()
            body = re.sub(r"/-.*?-/", "", body, flags=re.S).strip()
            body = re.sub(r"--.*", "", body).strip()
            if body.startswith("by"):
                body = body[2:].strip()
            if body.startswith("exact "):
                body = body[len("exact ") :].strip()
            direct = re.fullmatch(
                r"(?P<expr>(?:[a-z][A-Za-z0-9_']*|[A-Z])\.[A-Za-z_][A-Za-z0-9_']*)",
                body,
            )
            if direct:
                wrappers[match.group("name")] = direct.group("expr")
    return wrappers


def landing_has_theorem_or_lemma(
    landing: str,
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> bool:
    for name in re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*\b", landing):
        if declarations.get(name) in {"theorem", "lemma"} and name not in projection_wrappers:
            return True
    return False


def alignment_has_theorem_or_lemma_landing(
    obligation: dict[str, Any],
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> bool:
    alignment = obligation.get("source_output_alignment")
    if not isinstance(alignment, dict):
        return False
    missing = alignment.get("missing_landing_names") or []
    if isinstance(missing, str):
        missing = [missing] if missing.strip() else []
    if missing:
        return False
    raw = alignment.get("existing_local_declarations") or []
    if not isinstance(raw, list):
        return False
    for item in raw:
        if isinstance(item, dict):
            name = str(item.get("name") or "")
        else:
            name = str(item or "")
        if not name:
            continue
        if declarations.get(name) in {"theorem", "lemma"} and name not in projection_wrappers:
            return True
    return False


def latest_review_entry(pack: dict[str, Any]) -> dict[str, Any]:
    reviews = pack.get("review_history") or []
    if not isinstance(reviews, list):
        return {}
    candidates = [item for item in reviews if isinstance(item, dict)]
    if not candidates:
        return {}

    def review_key(item: dict[str, Any]) -> datetime:
        raw = str(item.get("reviewed_at") or "")
        try:
            return datetime.fromisoformat(raw.replace("Z", "+00:00"))
        except ValueError:
            return datetime.min.replace(tzinfo=UTC)

    return max(candidates, key=review_key)


def latest_review_marks_obligation_covered(pack: dict[str, Any], obligation_id: str) -> bool:
    review = latest_review_entry(pack)
    if str(review.get("verdict") or "").strip() != "pass":
        return False
    if str(review.get("status") or "").strip() != "covered":
        return False
    blockers = review.get("open_blockers") or []
    if not isinstance(blockers, list):
        return False
    for item in blockers:
        if not isinstance(item, dict):
            continue
        if str(item.get("obligation_id") or "") != obligation_id:
            continue
        if str(item.get("issue") or "").strip() == "covered":
            return True
    return False


def source_predicate_is_review_covered(
    pack: dict[str, Any],
    obligation: dict[str, Any],
) -> bool:
    if str(obligation.get("kind") or "").strip() != "source_step":
        return False
    if str(obligation.get("status") or "").strip() != "partial":
        return False
    if str(obligation.get("landing_kind") or "").strip() != "support_predicate":
        return False
    if str(obligation.get("proof_contract_status") or "").strip() != "not_applicable":
        return False
    return latest_review_marks_obligation_covered(pack, obligation_id(obligation))


def obligation_is_allowed_exception(task_id: str, obligation: dict[str, Any]) -> bool:
    if str(obligation.get("status") or "").strip() != "accepted_as_proof_debt":
        return False
    landing = obligation_landing(obligation)
    proof_contract_status = str(obligation.get("proof_contract_status") or "").strip()
    notes = str(obligation.get("proof_contract_notes") or "").lower()
    if task_id == "thm_14_8":
        return ALLOWED_PROOF_BEYOND_BOOK in landing or proof_contract_status == "beyond_book_exception"
    if task_id == "thm_11_8":
        return (
            proof_contract_status == "beyond_book_exception"
            and ("etemadi" in notes or "external" in notes or "strong_law" in landing)
        )
    return False


def task_is_allowed_exception(task_id: str, task: dict[str, Any], opens: list[str]) -> bool:
    if task_id in SOURCE_STATEMENT_EXCEPTION_TASKS:
        return (
            str(task.get("phase2_status") or "").strip() == "allowed_exception"
            and str(task.get("phase2_status_evidence_type") or "").strip()
            == "explicit_allowed_exception"
        )
    return (
        task_id in ALLOWED_EXCEPTION_TASKS
        and str(task.get("phase2_status") or "").strip() == "allowed_exception"
        and not opens
    )


def landing_analysis(
    landing: str,
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> dict[str, Any]:
    names = re.findall(r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)?\b", landing)
    theorem_or_lemma: list[str] = []
    projection_wrapper_theorems: list[dict[str, str]] = []
    known_decls: list[dict[str, str]] = []
    structure_fields: list[str] = []
    missing: list[str] = []
    for name in names:
        base = name.split(".", 1)[0]
        kind = declarations.get(name)
        if kind is None and "." in name:
            base_kind = declarations.get(base)
            if base_kind == "structure":
                structure_fields.append(name)
                known_decls.append({"name": base, "kind": base_kind})
                continue
        if kind is None:
            missing.append(name)
            continue
        known_decls.append({"name": name, "kind": kind})
        if kind in {"theorem", "lemma"}:
            theorem_or_lemma.append(name)
            if name in projection_wrappers:
                projection_wrapper_theorems.append(
                    {"name": name, "projection": projection_wrappers[name]}
                )
    problem = ""
    if landing and structure_fields and theorem_or_lemma:
        problem = "theorem_wrapper_over_structure_field"
    elif landing and theorem_or_lemma and len(projection_wrapper_theorems) == len(theorem_or_lemma):
        problem = "theorem_wrapper_over_projection_field"
    elif landing and not theorem_or_lemma:
        if structure_fields:
            problem = "structure_field_landing"
        elif missing:
            problem = "missing_theorem_or_lemma_landing"
        else:
            problem = "non_theorem_landing"
    elif not landing:
        problem = "empty_landing"
    return {
        "names": names,
        "known_declarations": known_decls,
        "theorem_or_lemma": theorem_or_lemma,
        "projection_wrapper_theorems": projection_wrapper_theorems,
        "structure_fields": structure_fields,
        "missing_names": missing,
        "has_theorem_or_lemma": bool(theorem_or_lemma)
        and len(projection_wrapper_theorems) < len(theorem_or_lemma),
        "problem": problem,
    }


def obligation_is_unresolved(
    task_id: str,
    pack: dict[str, Any],
    obligation: dict[str, Any],
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> bool:
    if obligation.get("blocking") is False:
        return False
    status = str(obligation.get("status") or "").strip()
    review_status = str(obligation.get("review_status") or "").strip()
    kind = str(obligation.get("kind") or "").strip()
    landing = obligation_landing(obligation)

    if status == "obsolete":
        return False
    if obligation_is_allowed_exception(task_id, obligation):
        return False
    if status == "proved" and review_status == "accepted":
        if kind == "proof_debt_support":
            return not (
                landing_has_theorem_or_lemma(landing, declarations, projection_wrappers)
                or alignment_has_theorem_or_lemma_landing(
                    obligation, declarations, projection_wrappers
                )
            )
        return False
    if source_predicate_is_review_covered(pack, obligation):
        return False
    if status == "accepted_as_proof_debt":
        return True
    if status in {"open", "in_progress", "partial", "blocked", "missing", "violated", ""}:
        return True
    if review_status in {"needs_review", "rejected", "unreviewed", ""}:
        return True
    return False


def open_obligations(
    root: Path,
    task_id: str,
    task: dict[str, Any],
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> list[str]:
    pack = read_json(proof_obligation_path(root, task_id))
    if isinstance(pack, dict) and isinstance(pack.get("obligations"), list):
        opens: list[str] = []
        for obligation in pack["obligations"]:
            if isinstance(obligation, dict) and obligation_is_unresolved(
                task_id, pack, obligation, declarations, projection_wrappers
            ):
                oid = obligation_id(obligation)
                if oid:
                    opens.append(oid)
        return opens
    summary = task.get("proof_obligation_summary") or {}
    raw = summary.get("open_blocking_ids") or []
    return [str(item) for item in raw]


def proof_obligation_path(root: Path, task_id: str) -> Path:
    return root / "phase2_prompt_packs" / task_id / "proof_obligations.json"


def obligation_id(obligation: dict[str, Any]) -> str:
    return str(obligation.get("id") or obligation.get("name") or obligation.get("title") or "")


def obligation_landing(obligation: dict[str, Any]) -> str:
    return str(obligation.get("lean_landing") or obligation.get("landing_decl") or "")


def summarize_proof_obligations(payload: dict[str, Any]) -> dict[str, Any]:
    obligations = payload.get("obligations", [])
    if not isinstance(obligations, list):
        obligations = []
    status_counts = Counter(
        str(item.get("status", "open") or "open")
        for item in obligations
        if isinstance(item, dict)
    )
    review_counts = Counter(
        str(item.get("review_status", "unreviewed") or "unreviewed")
        for item in obligations
        if isinstance(item, dict)
    )
    alignment_counts = Counter(
        str(item.get("source_output_alignment", {}).get("audit_class", "") or "unclassified")
        for item in obligations
        if isinstance(item, dict)
        and str(item.get("status", "") or "").strip().lower() == "accepted_as_proof_debt"
        and isinstance(item.get("source_output_alignment", {}), dict)
    )
    open_blocking_ids = [
        obligation_id(item)
        for item in obligations
        if isinstance(item, dict)
        and bool(item.get("blocking", True))
        and str(item.get("status", "open") or "open") not in PASSING_OBLIGATION_STATUSES
        and obligation_id(item)
    ]
    classification = payload.get("classification", {})
    if not isinstance(classification, dict):
        classification = {}
    scaffolds = payload.get("scaffold_hypotheses", [])
    if not isinstance(scaffolds, list):
        scaffolds = []
    placeholder_ids = [
        obligation_id(item)
        for item in obligations
        if isinstance(item, dict)
        and obligation_id(item) == PLACEHOLDER_OBLIGATION_ID
        and (
            "placeholder" in str(item.get("source_ref", "") or "").lower()
            or "placeholder" in str(item.get("notes", "") or "").lower()
            or not obligation_landing(item).strip()
        )
    ]
    requires_decomposition = bool(classification.get("requires_decomposition", False))
    concrete_obligations = [
        item
        for item in obligations
        if isinstance(item, dict) and obligation_id(item) not in set(placeholder_ids)
    ]
    return {
        "schema_version": str(
            payload.get("schema_version", "phase2.proof_obligations.v1")
            or "phase2.proof_obligations.v1"
        ),
        "task_id": str(payload.get("task_id", "") or ""),
        "requires_decomposition": requires_decomposition,
        "total_obligations": len([item for item in obligations if isinstance(item, dict)]),
        "status_counts": dict(status_counts),
        "review_status_counts": dict(review_counts),
        "source_output_alignment_counts": dict(alignment_counts),
        "open_blocking_ids": open_blocking_ids,
        "scaffold_hypothesis_count": len(scaffolds),
        "placeholder_obligation_ids": placeholder_ids,
        "needs_concrete_decomposition": requires_decomposition
        and (not concrete_obligations or bool(placeholder_ids)),
    }


def obligation_details(
    root: Path,
    task_id: str,
    open_ids: list[str],
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> list[dict[str, Any]]:
    pack = read_json(proof_obligation_path(root, task_id))
    if not isinstance(pack, dict):
        return []
    ledger = read_json(root / "project_ledger.json") or {}
    ledger_tasks = ledger.get("tasks") if isinstance(ledger, dict) else {}
    if not isinstance(ledger_tasks, dict):
        ledger_tasks = {}
    obligations = pack.get("obligations") or []
    if not isinstance(obligations, list):
        return []

    wanted = set(open_ids)
    details: list[dict[str, Any]] = []
    for obligation in obligations:
        if not isinstance(obligation, dict):
            continue
        oid = obligation_id(obligation)
        if wanted and oid not in wanted:
            continue
        if wanted or obligation_is_unresolved(
            task_id, pack, obligation, declarations, projection_wrappers
        ):
            child_task_id = str(obligation.get("ledger_task_id") or obligation.get("discharged_by_task") or "")
            child_task = ledger_tasks.get(child_task_id)
            if not isinstance(child_task, dict):
                child_task = {}
            child_output_exists = bool(child_task_id and output_path(root, child_task_id).exists())
            label = " ".join(
                str(obligation.get(field, ""))
                for field in ("id", "name", "title", "kind", "description", "statement")
            ).lower()
            details.append(
                {
                    "id": oid,
                    "name": str(obligation.get("name") or ""),
                    "title": str(obligation.get("title") or ""),
                    "kind": str(obligation.get("kind") or ""),
                    "status": str(obligation.get("status") or ""),
                    "review_status": str(obligation.get("review_status") or ""),
                    "lean_landing": obligation_landing(obligation),
                    "landing_analysis": landing_analysis(
                        obligation_landing(obligation), declarations, projection_wrappers
                    ),
                    "is_interface": "interface" in label,
                    "child_task_id": child_task_id,
                    "child_status": str(child_task.get("status") or ""),
                    "child_has_output": child_output_exists,
                }
            )
    return details


def accepted_proof_debt_count(task: dict[str, Any]) -> int:
    summary = task.get("proof_obligation_summary") or {}
    raw = summary.get("accepted_as_proof_debt") or 0
    try:
        return int(raw)
    except (TypeError, ValueError):
        return 0


def clean_debt_error_tasks(root: Path) -> set[str]:
    payload = read_json(root / CLEAN_DEBT_JSON)
    if not isinstance(payload, dict):
        return set()
    raw = payload.get("error_tasks") or []
    if isinstance(raw, dict):
        return {str(key) for key in raw}
    if isinstance(raw, list):
        return {str(item) for item in raw}
    return set()


def output_task_ids(root: Path, start_chapter: int, end_chapter: int) -> set[str]:
    output_dir = root / "ToyApollo" / "Output"
    ids: set[str] = set()
    if not output_dir.exists():
        return ids
    for path in output_dir.glob("*.lean"):
        task_id = path.stem
        if task_id.startswith("PackBuildCheck_") or task_id.startswith("PackVerify_"):
            continue
        if task_id_in_scope(task_id, start_chapter, end_chapter):
            ids.add(task_id)
    return ids


def output_importers(root: Path, task_id: str) -> list[str]:
    output_dir = root / "ToyApollo" / "Output"
    if not output_dir.exists():
        return []
    needle = f"import ToyApollo.Output.{task_id}"
    importers: list[str] = []
    for path in sorted(output_dir.glob("*.lean")):
        if path.stem == task_id:
            continue
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        if needle in text:
            importers.append(path.stem)
    return importers


def orphan_outputs_payload(root: Path, output_ids: set[str], task_ids: set[str]) -> list[dict[str, Any]]:
    payload: list[dict[str, Any]] = []
    for task_id in sorted(output_ids - task_ids, key=lambda item: (chapter_for_task_id(item) or 999, item)):
        path = output_path(root, task_id)
        has_prompt_pack = proof_obligation_path(root, task_id).exists() or (
            root / "phase2_prompt_packs" / task_id
        ).exists()
        payload.append(
            {
                "task_id": task_id,
                "chapter": chapter_for_task_id(task_id),
                "file": rel(path, root),
                "has_prompt_pack": has_prompt_pack,
                "imported_by": output_importers(root, task_id),
                "reasons": ["missing_ledger_entry"],
                "action_bucket": "support_output_without_ledger",
                "next_action": "Verify whether this is an intentional support module imported by a real task; build-check it, but do not count it as a task by itself.",
            }
        )
    return payload


def action_bucket_for(reasons: list[str]) -> str:
    reason_set = set(reasons)
    if "build_failed" in reason_set or "build_timeout" in reason_set:
        return "build_repair"
    if "allowed_exception_boundary" in reason_set:
        return "allowed_exception_boundary"
    if "missing_output" in reason_set:
        return "missing_output"
    if "critical_ch6_bridge_verify" in reason_set and len(reason_set) == 1:
        return "critical_bridge_verification"
    if "metadata_drift_status_only" in reason_set:
        return "metadata_drift"
    if "public_surface_error" in reason_set and "open_obligations" in reason_set:
        return "public_surface_and_obligations"
    if "public_surface_error" in reason_set:
        return "public_surface_cleanup"
    if "open_obligations" in reason_set:
        return "obligation_resolution"
    if "completed_with_proof_debt" in reason_set:
        return "allowed_beyond_book_hygiene"
    if "accepted_proof_debt" in reason_set:
        return "proof_debt_review"
    if "critical_ch6_bridge_verify" in reason_set:
        return "critical_bridge_verification"
    return "status_review"


NEXT_ACTIONS = {
    "critical_bridge_verification": "Build-check the Chapter 6 bridge and keep it in the report as a critical dependency, even though it is already completed.",
    "metadata_drift": "Confirm the file builds and metadata is fresh, then update ledger/status without treating it as mathematical proof debt.",
    "public_surface_and_obligations": "First remove public Support/Spine parameters, then close the named proof obligations with theorem-level landings.",
    "public_surface_cleanup": "Remove public Support/Spine parameters or make support-consuming helpers private; no open obligation is recorded.",
    "obligation_resolution": "Resolve the open proof obligations and land them on theorem/lemma declarations rather than structure fields.",
    "allowed_beyond_book_hygiene": "Keep only the documented thm_14_8 beyond-book exception and make inherited uses explicit.",
    "proof_debt_review": "Review accepted proof debt and either retire it or document it as the allowed beyond-book exception.",
    "allowed_exception_boundary": "Keep the explicit allowed exception visible, but do not count it as unfinished proof debt.",
    "build_repair": "Fix Lean build failures before semantic cleanup.",
    "missing_output": "Regenerate or recover the missing output file before any proof-debt decision.",
    "status_review": "Inspect ledger history and latest verification artifacts to decide whether this is stale metadata or a real unfinished task.",
}


REPAIR_BUCKET_ORDER = [
    "critical_bridge_verification",
    "metadata_drift",
    "public_surface_and_obligations",
    "public_surface_cleanup",
    "obligation_resolution",
    "allowed_beyond_book_hygiene",
    "proof_debt_review",
    "allowed_exception_boundary",
    "build_repair",
    "missing_output",
    "status_review",
]


def repair_batches(items: list[dict[str, Any]]) -> list[dict[str, Any]]:
    groups: dict[str, list[str]] = {}
    for item in items:
        groups.setdefault(str(item["action_bucket"]), []).append(str(item["task_id"]))
    batches: list[dict[str, Any]] = []
    for bucket in REPAIR_BUCKET_ORDER:
        task_ids = groups.get(bucket)
        if not task_ids:
            continue
        batches.append(
            {
                "bucket": bucket,
                "count": len(task_ids),
                "task_ids": task_ids,
                "next_action": NEXT_ACTIONS[bucket],
            }
        )
    return batches


def _terminate_process_tree(proc: subprocess.Popen[str]) -> None:
    if proc.poll() is not None:
        return
    if os.name == "nt":
        subprocess.run(
            ["taskkill", "/PID", str(proc.pid), "/T", "/F"],
            text=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=False,
        )
        return
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        return


def build_result(root: Path, task_id: str, timeout_seconds: int) -> dict[str, Any]:
    path = output_path(root, task_id)
    if not path.exists():
        return {"checked": False, "status": "missing_output"}
    popen_kwargs: dict[str, Any] = {}
    if os.name == "nt":
        popen_kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        popen_kwargs["start_new_session"] = True
    proc = subprocess.Popen(
        ["lake", "env", "lean", str(path)],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        **popen_kwargs,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout_seconds)
    except subprocess.TimeoutExpired:
        _terminate_process_tree(proc)
        try:
            stdout, stderr = proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            stdout, stderr = "", ""
        return {
            "checked": True,
            "status": "timeout",
            "exit_code": None,
            "stderr_tail": stderr[-2000:],
            "stdout_tail": stdout[-2000:],
        }
    return {
        "checked": True,
        "status": "ok" if proc.returncode == 0 else "failed",
        "exit_code": proc.returncode,
        "stderr_tail": stderr[-2000:],
        "stdout_tail": stdout[-2000:],
    }


def lean_output_hash(content: str) -> str:
    return hashlib.md5(content.encode("utf-8")).hexdigest()


def extract_exported_symbols(lean_code: str) -> list[str]:
    symbols: list[str] = []
    matches = re.finditer(
        r"^\s*(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([a-zA-Z0-9_']+)",
        lean_code,
        re.MULTILINE,
    )
    for match in matches:
        symbols.append(match.group(1))
    return symbols


def apply_metadata_drift_fixes(
    root: Path,
    payload: dict[str, Any],
    *,
    build_timeout_seconds: int,
    build_checker: Any | None = None,
) -> dict[str, Any]:
    refuse_legacy_ledger_write(root, operation="unfinished-task metadata repair")
    checker = build_checker or build_result
    ledger_path = root / "project_ledger.json"
    ledger = read_json(ledger_path)
    if not isinstance(ledger, dict) or not isinstance(ledger.get("tasks"), dict):
        manifest = {
            "applied_at": utc_stamp(),
            "changed_task_count": 0,
            "changed_tasks": {},
            "skipped_tasks": {"<ledger>": "project_ledger.json missing or malformed"},
        }
        write_json(root / METADATA_FIX_MANIFEST, manifest)
        return manifest

    changed_tasks: dict[str, Any] = {}
    skipped_tasks: dict[str, str] = {}
    for item in payload.get("items", []):
        if not isinstance(item, dict) or item.get("action_bucket") != "metadata_drift":
            continue
        task_id = str(item.get("task_id", "") or "")
        if not task_id:
            continue
        build = checker(root, task_id, build_timeout_seconds)
        if build.get("status") != "ok":
            skipped_tasks[task_id] = f"build status is {build.get('status')}"
            continue
        path = output_path(root, task_id)
        if not path.exists():
            skipped_tasks[task_id] = "output file is missing"
            continue
        task = ledger["tasks"].get(task_id)
        if not isinstance(task, dict):
            skipped_tasks[task_id] = "ledger task is missing"
            continue

        content = path.read_text(encoding="utf-8")
        symbols = extract_exported_symbols(content)
        old_status = task.get("status")
        old_output_hash = task.get("output_hash")
        old_symbols = list(task.get("exported_symbols") or [])
        task["status"] = "COMPLETED"
        task["output_hash"] = lean_output_hash(content)
        task["exported_symbols"] = symbols
        task["last_error"] = ""
        task["last_align_error"] = ""

        symbol_map = ledger.setdefault("symbols", {})
        if isinstance(symbol_map, dict):
            for symbol, owner in list(symbol_map.items()):
                if owner == task_id:
                    del symbol_map[symbol]
            for symbol in symbols:
                symbol_map[symbol] = task_id

        changed_tasks[task_id] = {
            "old_status": old_status,
            "new_status": "COMPLETED",
            "old_output_hash": old_output_hash,
            "new_output_hash": task["output_hash"],
            "old_exported_symbols": old_symbols,
            "new_exported_symbols": symbols,
        }

    if changed_tasks:
        ledger["phase2_unfinished_metadata_status_fix"] = {
            "applied_at": utc_stamp(),
            "changed_task_count": len(changed_tasks),
        }
        write_json(ledger_path, ledger)

    manifest = {
        "applied_at": utc_stamp(),
        "changed_task_count": len(changed_tasks),
        "changed_tasks": changed_tasks,
        "skipped_tasks": skipped_tasks,
    }
    write_json(root / METADATA_FIX_MANIFEST, manifest)
    return manifest


def _parent_task_id_from_payload(payload: dict[str, Any], task: dict[str, Any]) -> str:
    for key in ("parent_task_id", "parent_block_id"):
        value = str(payload.get(key) or task.get(key) or "").strip()
        if value:
            return value
    classification = payload.get("classification", {})
    evidence = classification.get("evidence", []) if isinstance(classification, dict) else []
    if isinstance(evidence, list):
        for item in evidence:
            match = re.search(r"\bparent_task_id=([A-Za-z0-9_'.-]+)", str(item))
            if match:
                return match.group(1)
    return ""


def _proof_obligation_pack_in_scope(
    task_id: str,
    payload: dict[str, Any],
    task: dict[str, Any],
    *,
    start_chapter: int,
    end_chapter: int,
    include_tasks: set[str],
) -> bool:
    if task_id in include_tasks or task_id_in_scope(task_id, start_chapter, end_chapter):
        return True
    parent_task_id = _parent_task_id_from_payload(payload, task)
    return parent_task_id in include_tasks or task_id_in_scope(
        parent_task_id, start_chapter, end_chapter
    )


def sync_ledger_proof_obligation_summaries(
    root: Path,
    *,
    start_chapter: int,
    end_chapter: int,
    include_tasks: list[str],
) -> dict[str, Any]:
    refuse_legacy_ledger_write(root, operation="proof-obligation ledger summary sync")
    ledger_path = root / "project_ledger.json"
    ledger = read_json(ledger_path)
    if not isinstance(ledger, dict) or not isinstance(ledger.get("tasks"), dict):
        manifest = {
            "applied_at": utc_stamp(),
            "changed_task_count": 0,
            "status_changed_task_count": 0,
            "changed_tasks": {},
            "skipped_tasks": {"<ledger>": "project_ledger.json missing or malformed"},
        }
        write_json(root / LEDGER_SUMMARY_SYNC_MANIFEST, manifest)
        return manifest

    include_set = set(include_tasks)
    changed_tasks: dict[str, Any] = {}
    skipped_tasks: dict[str, str] = {}
    tasks = ledger["tasks"]
    for path in sorted((root / "phase2_prompt_packs").glob("*/proof_obligations.json")):
        payload = read_json(path)
        if not isinstance(payload, dict):
            skipped_tasks[rel(path, root)] = "proof_obligations.json missing or malformed"
            continue
        task_id = str(payload.get("task_id") or path.parent.name)
        task = tasks.get(task_id)
        if not isinstance(task, dict):
            skipped_tasks[task_id] = "ledger task is missing"
            continue
        if not _proof_obligation_pack_in_scope(
            task_id,
            payload,
            task,
            start_chapter=start_chapter,
            end_chapter=end_chapter,
            include_tasks=include_set,
        ):
            continue

        new_summary = summarize_proof_obligations(payload)
        old_summary = task.get("proof_obligation_summary")
        old_status = str(task.get("status") or "")
        new_status = old_status
        open_blockers = new_summary.get("open_blocking_ids", [])
        if open_blockers and old_status in {"COMPLETED", "COMPLETED_WITH_PROOF_DEBT"}:
            new_status = "FAILED_LOCAL"

        if old_summary == new_summary and new_status == old_status:
            continue

        task["proof_obligations_file"] = rel(path, root)
        task["proof_obligation_summary"] = new_summary
        if new_status != old_status:
            task["status"] = new_status
        changed_tasks[task_id] = {
            "proof_obligations_file": rel(path, root),
            "old_status": old_status,
            "new_status": new_status,
            "old_open_blocking_ids": (
                old_summary.get("open_blocking_ids", []) if isinstance(old_summary, dict) else []
            ),
            "new_open_blocking_ids": open_blockers,
            "old_status_counts": (
                old_summary.get("status_counts", {}) if isinstance(old_summary, dict) else {}
            ),
            "new_status_counts": new_summary.get("status_counts", {}),
            "status_changed": new_status != old_status,
        }

    if changed_tasks:
        ledger["phase2_unfinished_ledger_summary_sync"] = {
            "applied_at": utc_stamp(),
            "changed_task_count": len(changed_tasks),
            "status_changed_task_count": sum(
                1 for item in changed_tasks.values() if item["status_changed"]
            ),
            "start_chapter": start_chapter,
            "end_chapter": end_chapter,
            "include_tasks": sorted(include_set),
        }
        write_json(ledger_path, ledger)

    manifest = {
        "applied_at": utc_stamp(),
        "changed_task_count": len(changed_tasks),
        "status_changed_task_count": sum(
            1 for item in changed_tasks.values() if item["status_changed"]
        ),
        "changed_tasks": changed_tasks,
        "skipped_tasks": skipped_tasks,
    }
    write_json(root / LEDGER_SUMMARY_SYNC_MANIFEST, manifest)
    return manifest


def classify_task(
    root: Path,
    task_id: str,
    task: dict[str, Any],
    public_error_tasks: set[str],
    critical_tasks: set[str],
    build: dict[str, Any] | None,
    declarations: dict[str, str],
    projection_wrappers: dict[str, str],
) -> dict[str, Any] | None:
    path = output_path(root, task_id)
    exists = path.exists()
    status = task.get("status")
    opens = open_obligations(root, task_id, task, declarations, projection_wrappers)
    open_details = obligation_details(root, task_id, opens, declarations, projection_wrappers)
    accepted_count = accepted_proof_debt_count(task)
    allowed_exception_boundary = task_is_allowed_exception(task_id, task, opens)
    reasons: list[str] = []

    if not task:
        reasons.append("missing_ledger_entry")
    elif allowed_exception_boundary:
        reasons.append("allowed_exception_boundary")
    elif status != "COMPLETED":
        reasons.append(f"ledger_status:{status}")
    if status == "COMPLETED_WITH_PROOF_DEBT" and not allowed_exception_boundary:
        reasons.append("completed_with_proof_debt")
    if opens:
        reasons.append("open_obligations")
    if accepted_count and not allowed_exception_boundary:
        reasons.append("accepted_proof_debt")
    if task_id in public_error_tasks:
        reasons.append("public_surface_error")
    if not exists:
        reasons.append("missing_output")
    if task_id in critical_tasks:
        reasons.append("critical_ch6_bridge_verify")
    if build is not None and build.get("checked"):
        if build.get("status") == "failed":
            reasons.append("build_failed")
        elif build.get("status") == "timeout":
            reasons.append("build_timeout")

    true_blockers = {
        "open_obligations",
        "accepted_proof_debt",
        "public_surface_error",
        "missing_output",
        "build_failed",
        "build_timeout",
        "completed_with_proof_debt",
    }
    if (
        task
        and status != "COMPLETED"
        and exists
        and not opens
        and accepted_count == 0
        and task_id not in public_error_tasks
        and not allowed_exception_boundary
        and not any(reason in true_blockers for reason in reasons)
    ):
        reasons.append("metadata_drift_status_only")

    if not reasons:
        return None

    action_bucket = action_bucket_for(reasons)

    return {
        "task_id": task_id,
        "chapter": chapter_for_task_id(task_id),
        "status": status,
        "file": rel(path, root),
        "output_exists": exists,
        "open_blocking_ids": opens,
        "open_obligation_details": open_details,
        "accepted_proof_debt_count": accepted_count,
        "reasons": reasons,
        "action_bucket": action_bucket,
        "next_action": NEXT_ACTIONS[action_bucket],
        "build": build,
    }


def build_inventory(
    root: Path,
    *,
    start_chapter: int,
    end_chapter: int,
    include_tasks: list[str],
    check_build: bool,
    build_timeout_seconds: int = 120,
    build_checker: Any | None = None,
    only_tasks: list[str] | None = None,
    only_buckets: list[str] | None = None,
) -> dict[str, Any]:
    ledger = read_json(root / "project_ledger.json") or {}
    tasks = ledger.get("tasks") or {}
    public_error_tasks = clean_debt_error_tasks(root)
    critical_tasks = set(include_tasks)
    declarations = declaration_kinds(root)
    projection_wrappers = theorem_projection_wrappers(root)

    output_ids = output_task_ids(root, start_chapter, end_chapter)
    candidate_ids: set[str] = set(include_tasks)
    requested_tasks = set(only_tasks or [])
    requested_buckets = set(only_buckets or [])
    candidate_ids.update(requested_tasks)
    ledger_task_ids: set[str] = set()
    for task_id, task in tasks.items():
        if not isinstance(task, dict) or not is_task_record(task_id, task):
            continue
        ledger_task_ids.add(task_id)
        if task_id_in_scope(task_id, start_chapter, end_chapter):
            candidate_ids.add(task_id)
        elif task_id in critical_tasks:
            candidate_ids.add(task_id)

    items: list[dict[str, Any]] = []
    checker = build_checker or build_result
    for task_id in sorted(candidate_ids, key=lambda item: (chapter_for_task_id(item) or 999, item)):
        if requested_tasks and task_id not in requested_tasks:
            continue
        task = tasks.get(task_id) if isinstance(tasks.get(task_id), dict) else {}
        item = classify_task(
            root, task_id, task, public_error_tasks, critical_tasks, None, declarations, projection_wrappers
        )
        if item is None:
            continue
        if requested_buckets and item["action_bucket"] not in requested_buckets:
            continue
        if check_build:
            build = checker(root, task_id, build_timeout_seconds)
            item = classify_task(
                root,
                task_id,
                task,
                public_error_tasks,
                critical_tasks,
                build,
                declarations,
                projection_wrappers,
            )
        if item is not None:
            items.append(item)

    reason_counts = Counter(reason for item in items for reason in item["reasons"])
    status_counts = Counter(str(item["status"]) for item in items)
    chapter_counts = Counter(str(item["chapter"]) for item in items)
    bucket_counts = Counter(str(item["action_bucket"]) for item in items)
    open_obligation_kind_counts = Counter(
        str(detail.get("kind") or "(missing)")
        for item in items
        for detail in item.get("open_obligation_details", [])
    )
    open_interface_obligation_count = sum(
        1
        for item in items
        for detail in item.get("open_obligation_details", [])
        if detail.get("is_interface")
    )
    structural_field_landing_count = sum(
        1
        for item in items
        for detail in item.get("open_obligation_details", [])
        if (detail.get("landing_analysis") or {}).get("structure_fields")
    )
    theorem_wrapper_structural_count = sum(
        1
        for item in items
        for detail in item.get("open_obligation_details", [])
        if (detail.get("landing_analysis") or {}).get("problem") == "theorem_wrapper_over_structure_field"
    )
    empty_landing_count = sum(
        1
        for item in items
        for detail in item.get("open_obligation_details", [])
        if (detail.get("landing_analysis") or {}).get("problem") == "empty_landing"
    )
    ledger_only_child_obligation_count = sum(
        1
        for item in items
        for detail in item.get("open_obligation_details", [])
        if detail.get("child_task_id") and not detail.get("child_has_output")
    )
    build_status_counts = Counter(
        str(item["build"]["status"])
        for item in items
        if isinstance(item.get("build"), dict) and item["build"].get("checked")
    )
    verification_only_count = sum(
        1
        for item in items
        if item.get("reasons") == ["critical_ch6_bridge_verify"]
    )
    allowed_exception_boundary_count = sum(
        1
        for item in items
        if item.get("action_bucket") == "allowed_exception_boundary"
    )
    blocking_unfinished_count = (
        len(items) - verification_only_count - allowed_exception_boundary_count
    )
    orphan_outputs = orphan_outputs_payload(root, output_ids, ledger_task_ids)
    return {
        "generated_at": utc_stamp(),
        "scope": {
            "start_chapter": start_chapter,
            "end_chapter": end_chapter,
            "include_tasks": include_tasks,
            "check_build": check_build,
            "build_timeout_seconds": build_timeout_seconds,
            "only_tasks": sorted(requested_tasks),
            "only_buckets": sorted(requested_buckets),
        },
        "summary": {
            "unfinished_or_verify_count": len(items),
            "blocking_unfinished_count": blocking_unfinished_count,
            "verification_only_count": verification_only_count,
            "allowed_exception_boundary_count": allowed_exception_boundary_count,
            "interpretation_notes": [
                "blocking_unfinished_count excludes verification-only items and explicit allowed-exception boundaries.",
                "allowed_exception_boundary items remain visible and are not ordinary clean proof completion.",
                "A zero blocking_unfinished_count does not claim external or beyond-book mathematics has been locally proved.",
            ],
            "orphan_output_count": len(orphan_outputs),
            "reason_counts": dict(sorted(reason_counts.items())),
            "bucket_counts": dict(sorted(bucket_counts.items())),
            "build_status_counts": dict(sorted(build_status_counts.items())),
            "status_counts": dict(sorted(status_counts.items())),
            "chapter_counts": dict(sorted(chapter_counts.items(), key=lambda pair: int(pair[0]))),
            "open_obligation_kind_counts": dict(sorted(open_obligation_kind_counts.items())),
            "open_interface_obligation_count": open_interface_obligation_count,
            "structural_field_landing_count": structural_field_landing_count,
            "theorem_wrapper_structural_count": theorem_wrapper_structural_count,
            "empty_landing_count": empty_landing_count,
            "ledger_only_child_obligation_count": ledger_only_child_obligation_count,
            "clean_debt_error_task_count": len(public_error_tasks),
        },
        "items": items,
        "repair_batches": repair_batches(items),
        "orphan_outputs": orphan_outputs,
    }


def markdown_report(payload: dict[str, Any]) -> str:
    lines = [
        "# Phase2 Unfinished Task Audit",
        "",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Scope: chapters `{payload['scope']['start_chapter']}`-`{payload['scope']['end_chapter']}`",
        f"- Extra included tasks: `{', '.join(payload['scope']['include_tasks']) or '(none)'}`",
        f"- Task filter: `{', '.join(payload['scope'].get('only_tasks', [])) or '(none)'}`",
        f"- Bucket filter: `{', '.join(payload['scope'].get('only_buckets', [])) or '(none)'}`",
        f"- Build checked: `{payload['scope']['check_build']}`",
        f"- Build timeout seconds: `{payload['scope'].get('build_timeout_seconds', '(default)')}`",
        f"- Unfinished or verify count: `{payload['summary']['unfinished_or_verify_count']}`",
        f"- Blocking unfinished count: `{payload['summary'].get('blocking_unfinished_count', payload['summary']['unfinished_or_verify_count'])}`",
        f"- Verification-only count: `{payload['summary'].get('verification_only_count', 0)}`",
        f"- Allowed-exception boundary count: `{payload['summary'].get('allowed_exception_boundary_count', 0)}`",
        f"- Orphan output count: `{payload['summary']['orphan_output_count']}`",
        "",
        "## Reason Counts",
        "",
    ]
    for reason, count in payload["summary"]["reason_counts"].items():
        lines.append(f"- `{reason}`: {count}")
    notes = payload["summary"].get("interpretation_notes") or []
    if notes:
        lines.extend(["", "## Interpretation Notes", ""])
        for note in notes:
            lines.append(f"- {note}")
    if payload["summary"].get("open_obligation_kind_counts"):
        lines.extend(["", "## Open Obligation Kinds", ""])
        for kind, count in payload["summary"]["open_obligation_kind_counts"].items():
            lines.append(f"- `{kind}`: {count}")
        lines.append(
            f"- `interface-name matches`: {payload['summary'].get('open_interface_obligation_count', 0)}"
        )
        lines.append(
            f"- `structure-field landings`: {payload['summary'].get('structural_field_landing_count', 0)}"
        )
        lines.append(
            f"- `theorem wrappers over structure fields`: {payload['summary'].get('theorem_wrapper_structural_count', 0)}"
        )
        lines.append(
            f"- `empty landings`: {payload['summary'].get('empty_landing_count', 0)}"
        )
        lines.append(
            f"- `ledger-only child obligations`: {payload['summary'].get('ledger_only_child_obligation_count', 0)}"
        )
    if payload["summary"].get("build_status_counts"):
        lines.extend(["", "## Build Status Counts", ""])
        for status, count in payload["summary"]["build_status_counts"].items():
            lines.append(f"- `{status}`: {count}")
    lines.extend(["", "## Repair Batches", ""])
    for batch in payload.get("repair_batches", []):
        lines.append(f"- `{batch['bucket']}` ({batch['count']}): `{', '.join(batch['task_ids'])}`")
        lines.append(f"  - action: {batch['next_action']}")
    lines.extend(["", "## Tasks", ""])
    for item in payload["items"]:
        lines.append(
            f"- `{item['task_id']}` ch{item['chapter']} `{item['status']}` "
            f"`{item['file']}` `{item['action_bucket']}`: "
            f"{', '.join(f'`{reason}`' for reason in item['reasons'])}"
        )
        if item["open_blocking_ids"]:
            lines.append(f"  - open: `{', '.join(item['open_blocking_ids'])}`")
        for detail in item.get("open_obligation_details", []):
            interface = " interface" if detail.get("is_interface") else ""
            landing = detail.get("lean_landing") or "(none)"
            child = ""
            if detail.get("child_task_id"):
                child = (
                    f", child `{detail.get('child_task_id')}`"
                    f" `{detail.get('child_status')}`"
                    f" output `{detail.get('child_has_output')}`"
                )
            landing_problem = (detail.get("landing_analysis") or {}).get("problem") or ""
            problem = f", landing problem `{landing_problem}`" if landing_problem else ""
            lines.append(
                f"  - obligation `{detail.get('id')}` `{detail.get('kind')}`"
                f"{interface}: status `{detail.get('status')}`, landing `{landing}`"
                f"{problem}{child}"
            )
        if item.get("build") and item["build"].get("checked"):
            lines.append(f"  - build: `{item['build'].get('status')}`")
    if payload.get("orphan_outputs"):
        lines.extend(["", "## Orphan Output Files", ""])
        for item in payload["orphan_outputs"]:
            prompt_pack = "prompt_pack=yes" if item.get("has_prompt_pack") else "prompt_pack=no"
            imported_by = ", ".join(item.get("imported_by", [])) or "(none)"
            lines.append(
                f"- `{item['task_id']}` ch{item['chapter']} `{item['file']}`: "
                f"{', '.join(f'`{reason}`' for reason in item['reasons'])}; "
                f"`{prompt_pack}`; imported by `{imported_by}`"
            )
    return "\n".join(lines) + "\n"


def has_blocking_unfinished(payload: dict[str, Any]) -> bool:
    summary = payload.get("summary")
    if isinstance(summary, dict) and "blocking_unfinished_count" in summary:
        try:
            return int(summary["blocking_unfinished_count"]) > 0
        except (TypeError, ValueError):
            return True
    return bool(payload.get("items"))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start-chapter", type=int, default=9)
    parser.add_argument("--end-chapter", type=int, default=14)
    parser.add_argument("--include-task", action="append", default=["thm_6_7__lemma_1"])
    parser.add_argument("--task", action="append", dest="only_tasks", default=[])
    parser.add_argument("--bucket", action="append", dest="only_buckets", default=[])
    parser.add_argument("--check-build", action="store_true")
    parser.add_argument("--build-timeout-seconds", type=int, default=120)
    parser.add_argument("--apply-metadata-drift-fixes", action="store_true")
    parser.add_argument(
        "--sync-ledger-proof-obligations",
        action="store_true",
        help=(
            "Synchronize each scoped ledger proof_obligation_summary from its current "
            "proof_obligations.json. This only reopens completed statuses when the current "
            "pack still has open blockers; it never marks tasks completed."
        ),
    )
    parser.add_argument("--write-report", action="store_true")
    parser.add_argument("--report-json", default=REPORT_JSON)
    parser.add_argument("--report-md", default=REPORT_MD)
    parser.add_argument("--fail-on-unfinished", action="store_true")
    args = parser.parse_args()

    root = repo_root()
    payload = build_inventory(
        root,
        start_chapter=args.start_chapter,
        end_chapter=args.end_chapter,
        include_tasks=list(dict.fromkeys(args.include_task)),
        check_build=args.check_build,
        build_timeout_seconds=args.build_timeout_seconds,
        only_tasks=args.only_tasks,
        only_buckets=args.only_buckets,
    )

    metadata_fix_manifest = None
    summary_sync_manifest = None
    if args.sync_ledger_proof_obligations:
        summary_sync_manifest = sync_ledger_proof_obligation_summaries(
            root,
            start_chapter=args.start_chapter,
            end_chapter=args.end_chapter,
            include_tasks=list(dict.fromkeys(args.include_task)),
        )
        payload = build_inventory(
            root,
            start_chapter=args.start_chapter,
            end_chapter=args.end_chapter,
            include_tasks=list(dict.fromkeys(args.include_task)),
            check_build=args.check_build,
            build_timeout_seconds=args.build_timeout_seconds,
            only_tasks=args.only_tasks,
            only_buckets=args.only_buckets,
        )

    if args.apply_metadata_drift_fixes:
        metadata_fix_manifest = apply_metadata_drift_fixes(
            root,
            payload,
            build_timeout_seconds=args.build_timeout_seconds,
        )
        payload = build_inventory(
            root,
            start_chapter=args.start_chapter,
            end_chapter=args.end_chapter,
            include_tasks=list(dict.fromkeys(args.include_task)),
            check_build=args.check_build,
            build_timeout_seconds=args.build_timeout_seconds,
            only_tasks=args.only_tasks,
            only_buckets=args.only_buckets,
        )

    if args.write_report:
        write_json(root / args.report_json, payload)
        report_md_path = root / args.report_md
        report_md_path.parent.mkdir(parents=True, exist_ok=True)
        report_md_path.write_text(markdown_report(payload), encoding="utf-8")

    print(json.dumps(payload["summary"], indent=2, ensure_ascii=False))
    if metadata_fix_manifest is not None:
        print(
            json.dumps(
                {
                    "metadata_drift_fixes_changed_task_count": metadata_fix_manifest["changed_task_count"],
                    "metadata_drift_fixes_skipped_task_count": len(metadata_fix_manifest["skipped_tasks"]),
                },
                indent=2,
                ensure_ascii=False,
            )
        )
    if summary_sync_manifest is not None:
        print(
            json.dumps(
                {
                    "ledger_summary_sync_changed_task_count": summary_sync_manifest[
                        "changed_task_count"
                    ],
                    "ledger_summary_sync_status_changed_task_count": summary_sync_manifest[
                        "status_changed_task_count"
                    ],
                    "ledger_summary_sync_skipped_task_count": len(
                        summary_sync_manifest["skipped_tasks"]
                    ),
                },
                indent=2,
                ensure_ascii=False,
            )
        )
    if args.fail_on_unfinished and has_blocking_unfinished(payload):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
