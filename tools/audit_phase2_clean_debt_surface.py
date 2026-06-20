from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from dataclasses import asdict, dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Iterable


TASK_RE = re.compile(r"^(?:def|thm|prob|ex)_(?P<chapter>\d+)(?:_|$)")
DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)\b"
)
PUBLIC_DECL_RE = re.compile(r"^\s*(?:noncomputable\s+)?(?P<kind>theorem|lemma|def)\s+")
LEAN_AUDIT_NAME_PREFIX = r"(?:[A-Z][A-Za-z0-9_]*|[a-z][A-Za-z0-9_]*_[A-Za-z0-9_]*)"
PROOF_PACKAGE_SUFFIX = r"(?:Support|Spine|Verification|ProofBeyondBook|Interface)"
PROOF_PACKAGE_RE = re.compile(
    r"\b"
    + LEAN_AUDIT_NAME_PREFIX
    + PROOF_PACKAGE_SUFFIX
    + r"\b"
)
IGNORED_PROOF_PACKAGE_NAMES = {
    # `Prob63Support` is the namespace/module prefix for the proved coupon
    # collector support from Problem 6.3, not a proof-package parameter.
    "Prob63Support",
}
PROOF_PACKAGE_PARAM_RE = re.compile(
    r"[\(\{\[][^\)\}\]]*:\s*[^\)\}\]]*\b"
    + LEAN_AUDIT_NAME_PREFIX
    + PROOF_PACKAGE_SUFFIX
    + r"\b"
    r"[^\)\}\]]*[\)\}\]]"
)
SETUP_RE = re.compile(r"\b" + LEAN_AUDIT_NAME_PREFIX + r"Setup\b")
SETUP_PARAM_RE = re.compile(
    r"[\(\{\[][^\)\}\]]*:\s*[^\)\}\]]*\b"
    + LEAN_AUDIT_NAME_PREFIX
    + r"Setup\b"
    r"[^\)\}\]]*[\)\}\]]"
)
BRIDGE_RE = re.compile(r"\b" + LEAN_AUDIT_NAME_PREFIX + r"Bridge\b")
BRIDGE_PARAM_RE = re.compile(
    r"\([^)]*:\s*[^)]*\b" + LEAN_AUDIT_NAME_PREFIX + r"Bridge\b[^)]*\)"
)
ALLOWED_PROOF_BEYOND_BOOK_TASK = "thm_14_8"
ALLOWED_PROOF_BEYOND_BOOK = "thm_14_8_ProofBeyondBook"
OPEN_STATUSES = {"open", "in_progress", "partial", "blocked"}
PASSING_STATUSES = {"proved", "obsolete", "accepted_as_proof_debt"}


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    file: str
    line: int


@dataclass(frozen=True)
class Finding:
    task_id: str
    file: str
    line: int
    category: str
    severity: str
    detail: str
    evidence: str
    action: str


def repo_root() -> Path:
    return Path(__file__).resolve().parents[1]


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def write_json(path: Path, payload: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def utc_stamp() -> str:
    return datetime.now(UTC).isoformat().replace("+00:00", "Z")


def rel(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def chapter_for_task_id(task_id: str) -> int | None:
    match = TASK_RE.match(task_id)
    if not match:
        return None
    return int(match.group("chapter"))


def is_task_in_scope(task_id: str, start_chapter: int, end_chapter: int) -> bool:
    chapter = chapter_for_task_id(task_id)
    return chapter is not None and start_chapter <= chapter <= end_chapter


def parent_task_id_from_payload(payload: dict[str, Any]) -> str:
    for key in ("parent_task_id", "parent_block_id"):
        value = str(payload.get(key) or "").strip()
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


def proof_obligation_pack_in_scope(
    task_id: str,
    payload: dict[str, Any],
    start_chapter: int,
    end_chapter: int,
) -> bool:
    if is_task_in_scope(task_id, start_chapter, end_chapter):
        return True
    parent_task_id = parent_task_id_from_payload(payload)
    return is_task_in_scope(parent_task_id, start_chapter, end_chapter)


def _iter_task_lean_files(path_iter: Iterable[Path], start_chapter: int, end_chapter: int) -> Iterable[Path]:
    seen: set[Path] = set()
    for path in sorted(path_iter):
        resolved = path.resolve()
        if resolved in seen:
            continue
        seen.add(resolved)
        if path.name.startswith("PackBuildCheck_") or path.name.startswith("PackVerify_"):
            continue
        task_id = path.stem
        if is_task_in_scope(task_id, start_chapter, end_chapter):
            yield path


def iter_output_files(
    root: Path,
    start_chapter: int,
    end_chapter: int,
    *,
    include_mirrors: bool = False,
) -> Iterable[Path]:
    paths: list[Path] = []
    output_dir = root / "ToyApollo" / "Output"
    if output_dir.exists():
        paths.extend(output_dir.glob("*.lean"))
    if include_mirrors:
        mirror_dir = root / "output_lean_files"
        if mirror_dir.exists():
            paths.extend(mirror_dir.rglob("*.lean"))
    yield from _iter_task_lean_files(paths, start_chapter, end_chapter)


def strip_lean_comments(source: str) -> str:
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(source):
        if depth == 0 and source.startswith("--", index):
            newline = source.find("\n", index)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
            continue
        if source.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if depth > 0:
            if source.startswith("/-", index):
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                depth -= 1
                index += 2
            else:
                if source[index] == "\n":
                    result.append("\n")
                index += 1
            continue
        result.append(source[index])
        index += 1
    return "".join(result)


def scan_declarations(root: Path) -> dict[str, Declaration]:
    declarations: dict[str, Declaration] = {}
    for path in sorted((root / "ToyApollo" / "Output").glob("*.lean")):
        clean = strip_lean_comments(read_text(path))
        for line_no, line in enumerate(clean.splitlines(), start=1):
            match = DECL_RE.match(line)
            if not match:
                continue
            declarations[match.group("name")] = Declaration(
                name=match.group("name"),
                kind=match.group("kind"),
                file=rel(path, root),
                line=line_no,
            )
    return declarations


def theorem_projection_wrappers(root: Path) -> dict[str, str]:
    wrappers: dict[str, str] = {}
    output_dir = root / "ToyApollo" / "Output"
    if not output_dir.exists():
        return wrappers
    for path in sorted(output_dir.glob("*.lean")):
        try:
            text = read_text(path)
        except OSError:
            continue
        clean = strip_lean_comments(text)
        decl_block_re = re.compile(DECL_RE.pattern, re.MULTILINE)
        matches = list(decl_block_re.finditer(clean))
        for index, match in enumerate(matches):
            if match.group("kind") not in {"theorem", "lemma"}:
                continue
            start = match.start()
            end = matches[index + 1].start() if index + 1 < len(matches) else len(clean)
            block = clean[start:end]
            if ":=" not in block:
                continue
            body = block.split(":=", 1)[1].strip()
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


def declaration_headers(source: str) -> Iterable[tuple[int, str]]:
    lines = strip_lean_comments(source).splitlines()
    index = 0
    while index < len(lines):
        line = lines[index]
        if not PUBLIC_DECL_RE.match(line):
            index += 1
            continue
        start = index + 1
        buffer = [line.strip()]
        cursor = index + 1
        while cursor < len(lines) and len(" ".join(buffer)) < 3000:
            current = lines[cursor].strip()
            if current:
                buffer.append(current)
            joined = " ".join(buffer)
            if ":=" in joined or re.search(r"\bby\b", joined) or re.search(r"\bwhere\b", joined):
                break
            cursor += 1
        yield start, " ".join(buffer)
        index = max(cursor + 1, index + 1)


def is_allowed_beyond_book(header_or_landing: str, task_id: str = "") -> bool:
    return ALLOWED_PROOF_BEYOND_BOOK in header_or_landing


def proof_package_names(source: str) -> list[str]:
    return sorted(
        {
            name
            for name in PROOF_PACKAGE_RE.findall(source)
            if name not in IGNORED_PROOF_PACKAGE_NAMES
        }
    )


def scan_public_surface(
    root: Path,
    start_chapter: int,
    end_chapter: int,
    *,
    include_mirrors: bool = False,
) -> list[Finding]:
    findings: list[Finding] = []
    for path in iter_output_files(root, start_chapter, end_chapter, include_mirrors=include_mirrors):
        task_id = path.stem
        for line, header in declaration_headers(read_text(path)):
            param_fragments = PROOF_PACKAGE_PARAM_RE.findall(header)
            packages = proof_package_names(" ".join(param_fragments))
            all_packages = proof_package_names(header)
            header_without_params = header
            for fragment in param_fragments:
                header_without_params = header_without_params.replace(fragment, " ")
            return_packages = proof_package_names(header_without_params)
            if packages:
                if all(package == ALLOWED_PROOF_BEYOND_BOOK for package in packages):
                    category = (
                        "allowed_beyond_book_surface"
                        if task_id == ALLOWED_PROOF_BEYOND_BOOK_TASK
                        else "inherited_beyond_book_surface"
                    )
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=line,
                            category=category,
                            severity="allowed",
                            detail=", ".join(packages),
                            evidence=header[:500],
                            action="Keep as the exact thm_14_8 proof-beyond-book exception; downstream use must remain marked as inherited exception, not ordinary proved debt.",
                        )
                    )
                elif return_packages:
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=line,
                            category="public_proof_package_parameter_in_support_proof_review",
                            severity="review",
                            detail=", ".join(packages),
                            evidence=header[:500],
                            action="Review as a theorem-level support-producing lemma; it should not be a task-facing final theorem.",
                        )
                    )
                else:
                    illegal = [package for package in packages if package != ALLOWED_PROOF_BEYOND_BOOK]
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=line,
                            category="public_proof_package_parameter",
                            severity="error",
                            detail=", ".join(illegal),
                            evidence=header[:500],
                            action="Replace the public parameter with internally constructed theorem-level evidence.",
                        )
                    )
            elif all_packages:
                findings.append(
                    Finding(
                        task_id=task_id,
                        file=rel(path, root),
                        line=line,
                        category="public_proof_package_return_review",
                        severity="review",
                        detail=", ".join(all_packages),
                        evidence=header[:500],
                        action="Review as theorem-level evidence for a support package; this is not a public support parameter by itself.",
                    )
                )
            bridges = sorted(set(BRIDGE_RE.findall(" ".join(BRIDGE_PARAM_RE.findall(header)))))
            if bridges:
                findings.append(
                    Finding(
                        task_id=task_id,
                        file=rel(path, root),
                        line=line,
                        category="public_interface_bridge_parameter_review",
                        severity="review",
                        detail=", ".join(bridges),
                        evidence=header[:500],
                        action="Review as interface translation; bridge parameters are not proof debt unless they carry unproved mathematics.",
                    )
                )
            setup_params = sorted(set(SETUP_RE.findall(" ".join(SETUP_PARAM_RE.findall(header)))))
            if setup_params:
                findings.append(
                    Finding(
                        task_id=task_id,
                        file=rel(path, root),
                        line=line,
                        category="public_setup_parameter_review",
                        severity="review",
                        detail=", ".join(setup_params),
                        evidence=header[:500],
                        action="Review whether this setup argument is only task data or is carrying unproved source/proof obligations through public fields.",
                    )
                )
    return findings


def landing_tokens(raw: str) -> list[str]:
    return re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", raw or "")


def landing_is_structure_field(raw: str, declarations: dict[str, Declaration]) -> bool:
    for token in landing_tokens(raw):
        if "." not in token:
            continue
        prefix = token.split(".", 1)[0]
        decl = declarations.get(prefix)
        if decl is not None and decl.kind == "structure":
            return True
        if PROOF_PACKAGE_RE.search(prefix) or BRIDGE_RE.search(prefix) or SETUP_RE.search(prefix):
            return True
    return False


def landing_resolves_only_to_nonproof(raw: str, declarations: dict[str, Declaration]) -> bool:
    tokens = [token.split(".", 1)[0] for token in landing_tokens(raw)]
    resolved = [declarations[token] for token in tokens if token in declarations]
    if not resolved:
        return False
    return all(decl.kind not in {"theorem", "lemma"} for decl in resolved)


def landing_is_projection_wrapper(raw: str, projection_wrappers: dict[str, str]) -> bool:
    for token in landing_tokens(raw):
        if token in projection_wrappers:
            return True
    return False


def proof_contract_verified(obligation: dict[str, Any]) -> bool:
    return (
        str(obligation.get("proof_contract_status", "") or "").strip() == "verified"
        and str(obligation.get("signature_match", "") or "").strip() == "passed"
        and str(obligation.get("body_reassumption_check", "") or "").strip() == "passed"
        and str(obligation.get("public_premise_check", "") or "").strip() == "passed"
    )


def scan_obligations(root: Path, start_chapter: int, end_chapter: int) -> list[Finding]:
    declarations = scan_declarations(root)
    projection_wrappers = theorem_projection_wrappers(root)
    findings: list[Finding] = []
    for path in sorted((root / "phase2_prompt_packs").glob("*/proof_obligations.json")):
        payload = read_json(path)
        if not isinstance(payload, dict):
            continue
        task_id = str(payload.get("task_id", "") or path.parent.name)
        if not proof_obligation_pack_in_scope(task_id, payload, start_chapter, end_chapter):
            continue
        obligations = payload.get("obligations", [])
        if not isinstance(obligations, list):
            continue
        for obligation in obligations:
            if not isinstance(obligation, dict):
                continue
            kind = str(obligation.get("kind", "") or "")
            status = str(obligation.get("status", "") or "")
            obligation_id = str(obligation.get("id", "") or "")
            landing = str(obligation.get("lean_landing", "") or obligation.get("landing", "") or "")
            evidence = f"{obligation_id}: {landing}".strip()
            if kind != "proof_debt_support":
                if proof_contract_verified(obligation):
                    continue
                if status == "proved" and landing_is_structure_field(landing, declarations):
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=0,
                            category="proved_obligation_lands_on_structure_field",
                            severity="error",
                            detail=obligation_id,
                            evidence=evidence,
                            action="Do not count a setup/interface/bridge field projection as discharged source evidence; add a theorem/lemma landing for the real proof step.",
                        )
                    )
                continue
            if status == "proved":
                if is_allowed_beyond_book(landing, task_id):
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=0,
                            category="allowed_beyond_book_obligation",
                            severity="allowed",
                            detail=obligation_id,
                            evidence=evidence,
                            action="Keep visible as the only permitted beyond-book exception; do not generalize this pattern.",
                        )
                    )
                elif not landing.strip():
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=0,
                            category="proved_proof_debt_without_landing",
                            severity="error",
                            detail=obligation_id,
                            evidence=evidence,
                            action="Reopen as a concrete obligation with a theorem-level landing, or prove and record the actual theorem.",
                        )
                    )
                elif landing_is_structure_field(landing, declarations):
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=0,
                            category="proved_proof_debt_lands_on_structure_field",
                            severity="error",
                            detail=obligation_id,
                            evidence=evidence,
                            action="Do not count a support/spine field projection as proof; replace it with a theorem/lemma landing.",
                        )
                    )
                elif landing_is_projection_wrapper(landing, projection_wrappers):
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=0,
                            category="proved_proof_debt_lands_on_projection_wrapper",
                            severity="error",
                            detail=obligation_id,
                            evidence=f"{evidence}; wrapper={projection_wrappers.get(landing.strip(), '')}".strip(),
                            action="Do not count a theorem that only returns a support/setup field projection as proof; replace it with the real theorem-level proof.",
                        )
                    )
                elif landing_resolves_only_to_nonproof(landing, declarations):
                    findings.append(
                        Finding(
                            task_id=task_id,
                            file=rel(path, root),
                            line=0,
                            category="proved_proof_debt_lands_on_nonproof_decl",
                            severity="error",
                            detail=obligation_id,
                            evidence=evidence,
                            action="Replace the nonproof landing with theorem-level evidence before marking the obligation proved.",
                        )
                    )
            elif status == "accepted_as_proof_debt" and not is_allowed_beyond_book(landing, task_id):
                findings.append(
                    Finding(
                        task_id=task_id,
                        file=rel(path, root),
                        line=0,
                        category="non_exception_accepted_debt",
                        severity="error",
                        detail=obligation_id,
                        evidence=evidence,
                        action="Promote this to an explicit task to clear; only ProofBeyondBook may remain accepted.",
                    )
                )
            elif status == "accepted_as_proof_debt" and is_allowed_beyond_book(landing, task_id):
                findings.append(
                    Finding(
                        task_id=task_id,
                        file=rel(path, root),
                        line=0,
                        category="allowed_beyond_book_obligation",
                        severity="allowed",
                        detail=obligation_id,
                        evidence=evidence,
                        action="Keep visible as the only permitted beyond-book exception; do not generalize this pattern.",
                    )
                )
    return findings


def summarize_obligations(payload: dict[str, Any]) -> dict[str, Any]:
    obligations = payload.get("obligations", [])
    if not isinstance(obligations, list):
        obligations = []
    status_counts = Counter(str(item.get("status", "open") or "open") for item in obligations if isinstance(item, dict))
    review_counts = Counter(str(item.get("review_status", "unreviewed") or "unreviewed") for item in obligations if isinstance(item, dict))
    open_blocking_ids = [
        str(item.get("id", "") or "")
        for item in obligations
        if isinstance(item, dict)
        and bool(item.get("blocking", True))
        and str(item.get("status", "open") or "open") not in PASSING_STATUSES
    ]
    classification = payload.get("classification", {})
    if not isinstance(classification, dict):
        classification = {}
    scaffolds = payload.get("scaffold_hypotheses", [])
    if not isinstance(scaffolds, list):
        scaffolds = []
    return {
        "schema_version": str(payload.get("schema_version", "phase2.proof_obligations.v1") or "phase2.proof_obligations.v1"),
        "task_id": str(payload.get("task_id", "") or ""),
        "requires_decomposition": bool(classification.get("requires_decomposition", False)),
        "total_obligations": len([item for item in obligations if isinstance(item, dict)]),
        "status_counts": dict(status_counts),
        "review_status_counts": dict(review_counts),
        "source_output_alignment_counts": {},
        "open_blocking_ids": open_blocking_ids,
        "scaffold_hypothesis_count": len(scaffolds),
        "placeholder_obligation_ids": [],
        "needs_concrete_decomposition": False,
    }


def _append_audit_note(obligation: dict[str, Any], message: str) -> None:
    notes = str(obligation.get("notes", "") or "").strip()
    if message in notes:
        return
    obligation["notes"] = f"{notes}\n{message}".strip() if notes else message


def _should_reopen_proved_debt(
    obligation: dict[str, Any],
    declarations: dict[str, Declaration],
    projection_wrappers: dict[str, str],
) -> tuple[bool, str]:
    landing = str(obligation.get("lean_landing", "") or obligation.get("landing", "") or "")
    if not landing.strip():
        return True, "proved proof_debt_support has no theorem-level landing"
    if landing_is_structure_field(landing, declarations):
        return True, "proved proof_debt_support lands on a support/spine structure field"
    if landing_is_projection_wrapper(landing, projection_wrappers):
        return True, "proved proof_debt_support lands on a theorem wrapper over a structure field"
    if landing_resolves_only_to_nonproof(landing, declarations):
        return True, "proved proof_debt_support lands only on non-theorem declarations"
    return False, ""


def apply_status_fixes(root: Path, start_chapter: int, end_chapter: int) -> dict[str, Any]:
    declarations = scan_declarations(root)
    projection_wrappers = theorem_projection_wrappers(root)
    changed_tasks: dict[str, dict[str, Any]] = {}
    stamp = utc_stamp()
    for path in sorted((root / "phase2_prompt_packs").glob("*/proof_obligations.json")):
        payload = read_json(path)
        if not isinstance(payload, dict):
            continue
        task_id = str(payload.get("task_id", "") or path.parent.name)
        if not proof_obligation_pack_in_scope(task_id, payload, start_chapter, end_chapter):
            continue
        obligations = payload.get("obligations", [])
        if not isinstance(obligations, list):
            continue
        task_changes: list[dict[str, Any]] = []
        for obligation in obligations:
            if not isinstance(obligation, dict):
                continue
            if str(obligation.get("kind", "") or "") != "proof_debt_support":
                continue
            obligation_id = str(obligation.get("id", "") or "")
            status = str(obligation.get("status", "") or "")
            landing = str(obligation.get("lean_landing", "") or obligation.get("landing", "") or "")
            is_beyond = is_allowed_beyond_book(landing, task_id)
            old = {
                "status": status,
                "review_status": str(obligation.get("review_status", "") or ""),
                "lean_landing": landing,
            }
            if is_beyond and status == "proved":
                obligation["status"] = "accepted_as_proof_debt"
                obligation["review_status"] = "accepted"
                obligation["blocking"] = True
                _append_audit_note(
                    obligation,
                    "[clean-debt-audit] Reclassified as the sole allowed beyond-book proof debt exception.",
                )
                task_changes.append({"obligation_id": obligation_id, "action": "proved_to_accepted_beyond_book", "old": old})
                continue
            if status == "proved":
                reopen, reason = _should_reopen_proved_debt(obligation, declarations, projection_wrappers)
                if reopen:
                    obligation["status"] = "open"
                    obligation["review_status"] = "needs_review"
                    obligation["blocking"] = True
                    _append_audit_note(obligation, f"[clean-debt-audit] Reopened on {stamp}: {reason}.")
                    task_changes.append({"obligation_id": obligation_id, "action": "proved_to_open", "reason": reason, "old": old})
            elif status == "accepted_as_proof_debt" and not is_beyond:
                obligation["status"] = "open"
                obligation["review_status"] = "needs_review"
                obligation["blocking"] = True
                _append_audit_note(
                    obligation,
                    f"[clean-debt-audit] Reopened on {stamp}: only thm_14_8_ProofBeyondBook may remain accepted proof debt.",
                )
                task_changes.append({"obligation_id": obligation_id, "action": "accepted_to_open_non_exception", "old": old})
        if task_changes:
            payload["clean_debt_surface_audit"] = {
                "applied_at": stamp,
                "status": "status_fixes_applied",
                "changes": task_changes,
            }
            write_json(path, payload)
            changed_tasks[task_id] = {
                "proof_obligations_file": rel(path, root),
                "changes": task_changes,
                "summary": summarize_obligations(payload),
            }
    ledger_path = root / "project_ledger.json"
    ledger = read_json(ledger_path)
    ledger_changes: dict[str, Any] = {}
    if isinstance(ledger, dict) and isinstance(ledger.get("tasks"), dict):
        for task_id, info in changed_tasks.items():
            task = ledger["tasks"].get(task_id)
            if not isinstance(task, dict):
                continue
            old_status = str(task.get("status", "") or "")
            summary = info["summary"]
            task["proof_obligation_summary"] = summary
            open_blockers = summary.get("open_blocking_ids", [])
            status_counts = summary.get("status_counts", {})
            accepted_count = int(status_counts.get("accepted_as_proof_debt", 0) or 0) if isinstance(status_counts, dict) else 0
            if open_blockers:
                task["status"] = "FAILED_LOCAL"
            elif accepted_count:
                task["status"] = "COMPLETED_WITH_PROOF_DEBT"
            ledger_changes[task_id] = {
                "old_status": old_status,
                "new_status": task.get("status", ""),
                "proof_obligation_summary": summary,
            }
        if ledger_changes:
            ledger["clean_debt_surface_audit"] = {
                "applied_at": stamp,
                "start_chapter": start_chapter,
                "end_chapter": end_chapter,
                "changed_task_count": len(ledger_changes),
            }
            write_json(ledger_path, ledger)
    manifest = {
        "applied_at": stamp,
        "start_chapter": start_chapter,
        "end_chapter": end_chapter,
        "changed_task_count": len(changed_tasks),
        "changed_tasks": changed_tasks,
        "ledger_changes": ledger_changes,
    }
    manifest_path = root / "docs" / "phase2_ch10_14_clean_debt_status_fix_manifest.json"
    write_json(manifest_path, manifest)
    return manifest


def findings_payload(findings: list[Finding]) -> dict[str, Any]:
    severity_counts = Counter(finding.severity for finding in findings)
    category_counts = Counter(finding.category for finding in findings)
    tasks = sorted({finding.task_id for finding in findings if finding.severity == "error"})
    return {
        "severity_counts": dict(sorted(severity_counts.items())),
        "category_counts": dict(sorted(category_counts.items())),
        "error_task_count": len(tasks),
        "error_tasks": tasks,
        "findings": [asdict(finding) for finding in findings],
    }


def render_markdown(
    payload: dict[str, Any],
    *,
    start_chapter: int,
    end_chapter: int,
    include_mirrors: bool = False,
) -> str:
    lines = [
        f"# Chapter {start_chapter}-{end_chapter} Clean Proof-Debt Surface Audit",
        "",
        "This report checks every official output task in scope, not only theorem tasks.",
        "The only allowed proof-debt exception is `thm_14_8_ProofBeyondBook`.",
        "",
        "## Summary",
        "",
        f"- include mirrors: `{include_mirrors}`",
    ]
    for key, value in payload["severity_counts"].items():
        lines.append(f"- {key}: {value}")
    lines.append(f"- error tasks: {payload['error_task_count']}")
    lines.extend(["", "## Category Counts", ""])
    for key, value in payload["category_counts"].items():
        lines.append(f"- {key}: {value}")
    lines.extend(["", "## Findings", ""])
    lines.append("| severity | category | task | location | detail | action |")
    lines.append("| --- | --- | --- | --- | --- | --- |")
    for finding in payload["findings"]:
        location = finding["file"]
        if finding["line"]:
            location = f"{location}:{finding['line']}"
        detail = finding["detail"].replace("|", "\\|")
        action = finding["action"].replace("|", "\\|")
        lines.append(
            f"| `{finding['severity']}` | `{finding['category']}` | `{finding['task_id']}` | "
            f"`{location}` | {detail} | {action} |"
        )
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit Chapter 10-14 public proof-debt surface.")
    parser.add_argument("--start-chapter", type=int, default=10)
    parser.add_argument("--end-chapter", type=int, default=14)
    parser.add_argument(
        "--include-mirrors",
        action="store_true",
        help="Also scan output_lean_files mirrors for stale public proof-package surfaces.",
    )
    parser.add_argument("--write-report", action="store_true")
    parser.add_argument("--apply-status-fixes", action="store_true")
    parser.add_argument("--fail-on-errors", action="store_true")
    args = parser.parse_args()

    root = repo_root()
    if args.apply_status_fixes:
        manifest = apply_status_fixes(root, args.start_chapter, args.end_chapter)
        print(
            json.dumps(
                {
                    "status_fixes_changed_task_count": manifest["changed_task_count"],
                    "ledger_changed_task_count": len(manifest["ledger_changes"]),
                },
                indent=2,
            )
        )
    findings = [
        *scan_public_surface(
            root,
            args.start_chapter,
            args.end_chapter,
            include_mirrors=args.include_mirrors,
        ),
        *scan_obligations(root, args.start_chapter, args.end_chapter),
    ]
    payload = findings_payload(findings)
    if args.write_report:
        report_name = "phase2_ch10_14_clean_debt_surface_audit"
        if args.include_mirrors:
            report_name += "_with_mirrors"
        report_base = root / "docs" / report_name
        write_json(report_base.with_suffix(".json"), payload)
        report_base.with_suffix(".md").write_text(
            render_markdown(
                payload,
                start_chapter=args.start_chapter,
                end_chapter=args.end_chapter,
                include_mirrors=args.include_mirrors,
            ),
            encoding="utf-8",
        )
    print(json.dumps({key: payload[key] for key in ("severity_counts", "category_counts", "error_task_count")}, indent=2))
    if args.fail_on_errors and payload["severity_counts"].get("error", 0):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
