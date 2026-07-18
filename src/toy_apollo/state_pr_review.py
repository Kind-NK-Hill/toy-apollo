from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

from src.block_id_naming import canonicalize_block_id

from .phase2_review_decision import evaluate_semantic_review_result
from .phase2_task_status import classify_phase2_task_status
from .state_reconcile import (
    ReconciliationError,
    _gh_json,
    discover_github_subjects,
    run_command,
    task_id_from_path,
)
from .state_store import (
    SubjectBundle,
    WorkspaceStateStore,
    sha256_file,
    sha256_json,
    utc_now,
)


class ExternalPrReviewError(RuntimeError):
    pass


@dataclass(frozen=True)
class PullRequestObservation:
    repo: str
    number: int
    state: str
    draft: bool
    base_sha: str
    head_sha: str
    head_repo: str
    head_ref: str
    changed_files: tuple[str, ...]
    affected_files: tuple[str, ...]
    subject: SubjectBundle
    url: str


def _json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ExternalPrReviewError(f"Invalid JSON artifact {path}: {exc}") from exc
    if not isinstance(payload, dict):
        raise ExternalPrReviewError(f"JSON artifact must contain an object: {path}")
    return payload


def _write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(
        json.dumps(dict(payload), indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _repo_slug(repo: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]+", "_", repo.strip()).strip("_") or "repository"


def _subject_payload(subject: SubjectBundle) -> dict[str, Any]:
    return {
        "schema": "toy-apollo.subject-bundle.v1",
        "subject_id": subject.subject_id,
        "task_id": subject.task_id,
        "subject_kind": subject.subject_kind,
        "source_repo": subject.source_repo,
        "source_commit": subject.source_commit,
        "layout": subject.layout,
        "primary_path": subject.primary_path,
        "primary_hash": subject.primary_hash,
        "bundle_hash": subject.bundle_hash,
        "files": subject.manifest(),
    }


def observe_pull_request(repo: str, number: int, task_id: str) -> PullRequestObservation:
    canonical_task = canonicalize_block_id(task_id)
    if not canonical_task:
        raise ExternalPrReviewError(f"Invalid task id: {task_id}")
    try:
        pull = _gh_json(f"repos/{repo}/pulls/{number}")
        files_payload = _gh_json(f"repos/{repo}/pulls/{number}/files", query={"per_page": "100"})
    except ReconciliationError as exc:
        raise ExternalPrReviewError(str(exc)) from exc
    if not isinstance(pull, Mapping) or not isinstance(files_payload, list):
        raise ExternalPrReviewError("GitHub returned an invalid pull-request observation.")

    changed_files = tuple(
        str(item.get("filename", "") or "")
        for item in files_payload
        if isinstance(item, Mapping) and str(item.get("filename", "") or "")
    )
    affected_files = tuple(path for path in changed_files if task_id_from_path(path) == canonical_task)
    if not affected_files:
        raise ExternalPrReviewError(
            f"PR #{number} does not change a file owned by task {canonical_task}."
        )

    head = pull.get("head") if isinstance(pull.get("head"), Mapping) else {}
    base = pull.get("base") if isinstance(pull.get("base"), Mapping) else {}
    head_repo_payload = head.get("repo") if isinstance(head.get("repo"), Mapping) else {}
    head_repo = str(head_repo_payload.get("full_name", "") or "")
    head_sha = str(head.get("sha", "") or "")
    base_sha = str(base.get("sha", "") or "")
    if not head_repo or not head_sha or not base_sha:
        raise ExternalPrReviewError("PR observation is missing exact base/head identity.")
    try:
        resolved_head, subjects = discover_github_subjects(
            repo=head_repo,
            ref=head_sha,
            source_repo="kenneth_pr",
            layout="kenneth",
            task_ids=[canonical_task],
        )
    except ReconciliationError as exc:
        raise ExternalPrReviewError(str(exc)) from exc
    subject = subjects.get(canonical_task)
    if resolved_head != head_sha or subject is None:
        raise ExternalPrReviewError(
            f"Could not resolve task {canonical_task} at exact PR head {head_sha}."
        )
    return PullRequestObservation(
        repo=repo,
        number=number,
        state=str(pull.get("state", "") or "").lower(),
        draft=bool(pull.get("draft")),
        base_sha=base_sha,
        head_sha=head_sha,
        head_repo=head_repo,
        head_ref=str(head.get("ref", "") or ""),
        changed_files=changed_files,
        affected_files=affected_files,
        subject=subject,
        url=str(pull.get("html_url", "") or ""),
    )


def _require_reviewable_pr(observation: PullRequestObservation) -> None:
    if observation.state != "open":
        raise ExternalPrReviewError(
            f"PR #{observation.number} is {observation.state or 'not open'}; exact-head review requires an open PR."
        )
    if not observation.draft:
        raise ExternalPrReviewError(
            f"PR #{observation.number} must remain draft while its exact head is under review."
        )


def _module_name(primary_path: str) -> str:
    path = Path(primary_path.replace("/", "\\"))
    return ".".join(path.with_suffix("").parts)


def verify_exact_checkout(
    checkout: Path,
    observation: PullRequestObservation,
    *,
    timeout: int = 1800,
) -> dict[str, Any]:
    checkout = checkout.expanduser().resolve()
    if not checkout.is_dir():
        raise ExternalPrReviewError(f"Checkout does not exist: {checkout}")
    head_result = run_command(["git", "-C", str(checkout), "rev-parse", "HEAD"])
    if head_result.returncode != 0:
        raise ExternalPrReviewError(f"Not a readable Git checkout: {checkout}")
    local_head = head_result.text.strip()
    if local_head != observation.head_sha:
        raise ExternalPrReviewError(
            f"Checkout HEAD {local_head} does not match PR head {observation.head_sha}."
        )
    status_result = run_command(
        ["git", "-C", str(checkout), "status", "--porcelain=v1", "--untracked-files=all"]
    )
    if status_result.returncode != 0 or status_result.text.strip():
        raise ExternalPrReviewError("Exact PR build checkout must be clean before review preparation.")

    primary_file = checkout / Path(observation.subject.primary_path.replace("/", "\\"))
    if not primary_file.is_file():
        raise ExternalPrReviewError(f"Exact PR primary file is missing: {primary_file}")
    if sha256_file(primary_file) != observation.subject.primary_hash:
        raise ExternalPrReviewError("Checkout primary file does not match the GitHub PR subject hash.")
    module = _module_name(observation.subject.primary_path)
    build = run_command(["lake", "build", module], cwd=checkout, timeout=timeout)
    receipt = {
        "schema": "toy-apollo.external-pr-build.v1",
        "task_id": observation.subject.task_id,
        "repo": observation.repo,
        "pr_number": observation.number,
        "base_sha": observation.base_sha,
        "head_sha": observation.head_sha,
        "subject_id": observation.subject.subject_id,
        "bundle_hash": observation.subject.bundle_hash,
        "primary_hash": observation.subject.primary_hash,
        "module": module,
        "command": ["lake", "build", module],
        "checkout": str(checkout),
        "success": build.returncode == 0,
        "returncode": build.returncode,
        "stdout": build.text,
        "stderr": build.error_text,
        "checked_at": utc_now(),
    }
    if build.returncode != 0:
        raise ExternalPrReviewError(
            f"Exact PR build failed for {module}: {build.error_text.strip() or build.text.strip()}"
        )
    after_status = run_command(
        ["git", "-C", str(checkout), "status", "--porcelain=v1", "--untracked-files=all"]
    )
    if after_status.returncode != 0 or after_status.text.strip():
        raise ExternalPrReviewError("Exact PR build changed tracked or untracked checkout files.")
    return receipt


def _external_pack_root(settings, observation: PullRequestObservation) -> Path:
    state_path = Path(settings.state_db_file).expanduser().resolve()
    return (
        state_path.parent
        / "external_pr_reviews"
        / _repo_slug(observation.repo)
        / f"pr_{observation.number}"
        / observation.head_sha
        / observation.subject.task_id
    )


def prepare_external_pr_review(
    *,
    settings,
    store: WorkspaceStateStore,
    repo: str,
    pr_number: int,
    task_id: str,
    checkout: Path,
    timeout: int = 1800,
    observer: Callable[[str, int, str], PullRequestObservation] = observe_pull_request,
    checkout_verifier: Callable[..., dict[str, Any]] = verify_exact_checkout,
) -> dict[str, Any]:
    store.assert_integrity()
    observation = observer(repo, pr_number, task_id)
    _require_reviewable_pr(observation)
    pack_dir = _external_pack_root(settings, observation)
    metadata_path = pack_dir / "external_pr_subject.json"
    if metadata_path.is_file():
        existing = _json_object(metadata_path)
        existing_input = Path(str(existing.get("review_input_file", "") or "")).expanduser()
        existing_build = Path(str(existing.get("build_result_file", "") or "")).expanduser()
        if (
            existing.get("head_sha") == observation.head_sha
            and existing.get("subject_id") == observation.subject.subject_id
            and list(existing.get("changed_files", [])) == list(observation.changed_files)
            and existing_input.is_file()
            and existing_build.is_file()
            and sha256_json(_json_object(existing_input)) == existing.get("review_input_hash")
            and sha256_file(existing_build) == existing.get("build_result_hash")
        ):
            return {**existing, "metadata_file": str(metadata_path), "reused": True}
        raise ExternalPrReviewError(f"Existing external review pack is inconsistent: {metadata_path}")

    pack_dir.mkdir(parents=True, exist_ok=True)
    try:
        build_receipt = checkout_verifier(checkout, observation, timeout=timeout)
    except ExternalPrReviewError:
        raise
    build_result_path = pack_dir / "external_pr_build_result.json"
    _write_json(build_result_path, build_receipt)
    if not bool(build_receipt.get("success")):
        raise ExternalPrReviewError(f"Exact PR build did not pass: {build_result_path}")

    from .core import open_runtime_ledger
    from .phase2_prompt_pack import (
        _write_codex_handoff_review_artifacts,
        resolve_phase2_task,
    )

    ledger = open_runtime_ledger(settings)
    task = resolve_phase2_task(observation.subject.task_id, ledger, settings)
    subject_bundle = _subject_payload(observation.subject)
    external_basis = {
        "external_subject": {
            "kind": "kenneth_pr_exact_head",
            "repo": observation.repo,
            "pr_number": observation.number,
            "url": observation.url,
            "draft": observation.draft,
            "base_sha": observation.base_sha,
            "head_sha": observation.head_sha,
            "head_repo": observation.head_repo,
            "head_ref": observation.head_ref,
            "changed_files": list(observation.changed_files),
            "affected_files": list(observation.affected_files),
            "subject_id": observation.subject.subject_id,
            "bundle_hash": observation.subject.bundle_hash,
            "build_result_file": str(build_result_path),
            "build_result_hash": sha256_file(build_result_path),
        }
    }
    context_suffix = "\n".join(
        [
            "# Exact external PR subject",
            "",
            f"- Repository: `{observation.repo}`",
            f"- Pull request: `#{observation.number}` ({observation.url})",
            f"- Draft during review: `{str(observation.draft).lower()}`",
            f"- Base SHA: `{observation.base_sha}`",
            f"- Head SHA: `{observation.head_sha}`",
            f"- Exact subject id: `{observation.subject.subject_id}`",
            f"- Exact bundle hash: `{observation.subject.bundle_hash}`",
            f"- Verified clean checkout: `{checkout.expanduser().resolve()}`",
            f"- Exact-head build receipt: `{build_result_path}`",
            "- This review covers the PR head bundle only. It does not cover Toy Output or MAT by similarity.",
        ]
    )
    artifacts = _write_codex_handoff_review_artifacts(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        attempt=1,
        candidate_path=Path(observation.subject.primary_path),
        candidate_code=(checkout / Path(observation.subject.primary_path.replace("/", "\\"))).read_text(encoding="utf-8"),
        build_summary=build_receipt,
        mode="external-pr-review",
        review_subject_kind="external_pr",
        build_result_file=str(build_result_path),
        build_candidate_file=observation.subject.primary_path,
        build_candidate_hash=observation.subject.primary_hash,
        subject_bundle_override=subject_bundle,
        review_basis_subject_file=checkout / Path(observation.subject.primary_path.replace("/", "\\")),
        review_basis_extra=external_basis,
        review_context_suffix=context_suffix,
        materialize_proof_obligations=False,
    )
    review_input_path = Path(str(artifacts["review_input_file"]))
    review_input = _json_object(review_input_path)
    metadata = {
        "schema": "toy-apollo.external-pr-review.v1",
        "task_id": observation.subject.task_id,
        "repo": observation.repo,
        "pr_number": observation.number,
        "url": observation.url,
        "draft": observation.draft,
        "base_sha": observation.base_sha,
        "head_sha": observation.head_sha,
        "head_repo": observation.head_repo,
        "head_ref": observation.head_ref,
        "changed_files": list(observation.changed_files),
        "affected_files": list(observation.affected_files),
        "subject_id": observation.subject.subject_id,
        "bundle_hash": observation.subject.bundle_hash,
        "primary_hash": observation.subject.primary_hash,
        "primary_path": observation.subject.primary_path,
        "build_result_file": str(build_result_path),
        "build_result_hash": sha256_file(build_result_path),
        "review_input_file": str(review_input_path),
        "review_input_hash": sha256_json(review_input),
        "review_prompt_file": str(artifacts["review_prompt_file"]),
        "review_context_file": str(artifacts["review_context_file"]),
        "review_result_template_file": str(artifacts["review_result_template_file"]),
        "expected_review_result_file": str(artifacts["expected_review_result_file"]),
        "prepared_at": utc_now(),
    }
    _write_json(metadata_path, metadata)

    store.upsert_subject(observation.subject)
    store.set_task_head(
        task_id=observation.subject.task_id,
        role="kenneth_pr_head",
        subject_id=observation.subject.subject_id,
        detail={"repo": repo, "pr_number": pr_number, "head_sha": observation.head_sha},
    )
    store.record_integration(
        task_id=observation.subject.task_id,
        target_repo="kenneth",
        integration_kind="pull_request",
        state=observation.state,
        branch=observation.head_ref,
        pr_number=observation.number,
        head_sha=observation.head_sha,
        head_subject_id=observation.subject.subject_id,
        remote_freshness="fresh",
        detail={"url": observation.url, "draft": observation.draft, "exact_review_pack": str(metadata_path)},
    )
    store.record_run(
        task_id=observation.subject.task_id,
        operation="external_pr_review_prepare",
        status="completed",
        subject_id=observation.subject.subject_id,
        artifact_path=metadata_path,
        detail={"repo": repo, "pr_number": pr_number, "head_sha": observation.head_sha},
        completed_at=utc_now(),
    )
    return {**metadata, "metadata_file": str(metadata_path), "reused": False}


def apply_external_pr_review(
    *,
    settings,
    store: WorkspaceStateStore,
    metadata_path: Path,
    result_path: Path,
    observer: Callable[[str, int, str], PullRequestObservation] = observe_pull_request,
) -> dict[str, Any]:
    del settings
    store.assert_integrity()
    metadata_path = metadata_path.expanduser().resolve()
    result_path = result_path.expanduser().resolve()
    metadata = _json_object(metadata_path)
    task_id = canonicalize_block_id(str(metadata.get("task_id", "") or ""))
    repo = str(metadata.get("repo", "") or "")
    pr_number = int(metadata.get("pr_number", 0) or 0)
    if not task_id or not repo or not pr_number:
        raise ExternalPrReviewError("External PR review metadata is missing task/repository/PR identity.")

    observation = observer(repo, pr_number, task_id)
    _require_reviewable_pr(observation)
    expected_identity = {
        "base_sha": observation.base_sha,
        "head_sha": observation.head_sha,
        "subject_id": observation.subject.subject_id,
        "bundle_hash": observation.subject.bundle_hash,
        "primary_hash": observation.subject.primary_hash,
    }
    for field, expected in expected_identity.items():
        if str(metadata.get(field, "") or "") != str(expected):
            raise ExternalPrReviewError(
                f"PR changed since review preparation: {field} no longer matches."
            )
    if list(metadata.get("changed_files", [])) != list(observation.changed_files):
        raise ExternalPrReviewError("PR file set changed since review preparation.")

    build_path = Path(str(metadata.get("build_result_file", "") or "")).expanduser().resolve()
    build_receipt = _json_object(build_path)
    if sha256_file(build_path) != str(metadata.get("build_result_hash", "") or ""):
        raise ExternalPrReviewError("Exact-head build receipt changed after review preparation.")
    for field, expected in (
        ("success", True),
        ("task_id", task_id),
        ("head_sha", observation.head_sha),
        ("subject_id", observation.subject.subject_id),
        ("bundle_hash", observation.subject.bundle_hash),
        ("primary_hash", observation.subject.primary_hash),
    ):
        if build_receipt.get(field) != expected:
            raise ExternalPrReviewError(f"Exact-head build receipt field {field} is invalid.")

    review_input_path = Path(str(metadata.get("review_input_file", "") or "")).expanduser().resolve()
    review_input = _json_object(review_input_path)
    if sha256_json(review_input) != str(metadata.get("review_input_hash", "") or ""):
        raise ExternalPrReviewError("Semantic review input changed after exact PR preparation.")
    subject_bundle = review_input.get("subject_bundle")
    if not isinstance(subject_bundle, Mapping):
        raise ExternalPrReviewError("Semantic review input has no exact subject bundle.")
    if (
        subject_bundle.get("bundle_hash") != observation.subject.bundle_hash
        or subject_bundle.get("primary_hash") != observation.subject.primary_hash
        or review_input.get("review_subject_kind") != "external_pr"
    ):
        raise ExternalPrReviewError("Semantic review input is not bound to the current exact PR subject.")

    from .phase2_semantic_review import render_semantic_review_prompt

    prompt_path = Path(str(metadata.get("review_prompt_file", "") or "")).expanduser().resolve()
    try:
        prompt_text = prompt_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ExternalPrReviewError(f"Bound semantic review prompt is missing: {prompt_path}") from exc
    if prompt_text.strip() != render_semantic_review_prompt(review_input).strip():
        raise ExternalPrReviewError("Semantic review prompt changed after exact PR preparation.")
    context_path = Path(str(metadata.get("review_context_file", "") or "")).expanduser().resolve()
    try:
        context_text = context_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ExternalPrReviewError(f"Bound semantic review context is missing: {context_path}") from exc
    if context_text.strip() != str(review_input.get("review_context_markdown", "") or "").strip():
        raise ExternalPrReviewError("Semantic review context changed after exact PR preparation.")

    raw_result = _json_object(result_path)
    decision = evaluate_semantic_review_result(
        raw_result,
        review_input=review_input,
        runner_metadata={"status": "external_pr_exact_head_apply", "metadata_file": str(metadata_path)},
    )
    if not decision.is_semantic_verdict or decision.task_status_projection is None:
        reason = str(decision.result.get("normalization_reason", "") or "invalid semantic review result")
        raise ExternalPrReviewError(reason)

    normalized = decision.result
    reviewer_independence = normalized.get("reviewer_independence", {})
    if isinstance(reviewer_independence, Mapping):
        reviewer_independence = json.dumps(
            dict(reviewer_independence), ensure_ascii=False, sort_keys=True
        )
    phase2_status = decision.task_status_projection.task_status
    store.upsert_subject(observation.subject)
    review_id = store.record_review(
        task_id=task_id,
        subject_id=observation.subject.subject_id,
        verdict=str(normalized.get("verdict", "") or ""),
        proof_class=str(normalized.get("proof_class", "") or ""),
        completion_class=str(normalized.get("completion_class", "") or ""),
        phase2_status=phase2_status,
        evidence_path=result_path,
        evidence_hash=sha256_file(result_path),
        reviewer_independence=str(reviewer_independence),
        authority_scope="kenneth_pr_exact_head_review",
        authority_eligible=decision.is_clean_pass,
    )
    store.set_task_head(
        task_id=task_id,
        role="kenneth_pr_head",
        subject_id=observation.subject.subject_id,
        detail={
            "repo": repo,
            "pr_number": pr_number,
            "head_sha": observation.head_sha,
            "review_id": review_id,
        },
    )
    store.record_run(
        task_id=task_id,
        operation="external_pr_review_apply",
        status="completed" if decision.is_clean_pass else "failed",
        subject_id=observation.subject.subject_id,
        artifact_path=result_path,
        detail={
            "repo": repo,
            "pr_number": pr_number,
            "head_sha": observation.head_sha,
            "review_id": review_id,
            "phase2_status": phase2_status,
        },
        completed_at=utc_now(),
    )
    return {
        "task_id": task_id,
        "repo": repo,
        "pr_number": pr_number,
        "head_sha": observation.head_sha,
        "subject_id": observation.subject.subject_id,
        "bundle_hash": observation.subject.bundle_hash,
        "review_id": review_id,
        "verdict": normalized.get("verdict", ""),
        "proof_class": normalized.get("proof_class", ""),
        "completion_class": normalized.get("completion_class", ""),
        "phase2_status": phase2_status,
        "exact_head_covered": bool(decision.is_clean_pass),
        "pr_mutated": False,
    }


def _matching_exact_binding(
    binding: Mapping[str, Any], observation: PullRequestObservation
) -> bool:
    return bool(
        str(binding.get("repo", "") or "") == observation.repo
        and int(binding.get("pull_request", 0) or 0) == observation.number
        and str(binding.get("base_commit", "") or "") == observation.base_sha
        and str(binding.get("head_commit", "") or "") == observation.head_sha
        and list(binding.get("changed_files", observation.changed_files))
        == list(observation.changed_files)
        and str(binding.get("candidate_primary_content_sha256", "") or "")
        == observation.subject.primary_hash
        and str(binding.get("exact_pr_bundle_hash", "") or "")
        == observation.subject.bundle_hash
        and str(binding.get("integration_head_subject_id", "") or "")
        == observation.subject.subject_id
    )


def _validate_builder_evidence(
    evidence: Mapping[str, Any], observation: PullRequestObservation
) -> None:
    if str(evidence.get("schema_version", "") or "") != "toy-apollo.kenneth-pr-exact-builder-evidence.v1":
        raise ExternalPrReviewError("Builder evidence schema is not supported.")
    if canonicalize_block_id(str(evidence.get("task_id", "") or "")) != observation.subject.task_id:
        raise ExternalPrReviewError("Builder evidence task does not match the PR subject.")
    subject = evidence.get("exact_subject")
    checks = evidence.get("checks")
    if not isinstance(subject, Mapping) or not isinstance(checks, Mapping):
        raise ExternalPrReviewError("Builder evidence is missing exact_subject/checks.")
    normalized_subject = {
        "repo": subject.get("repo"),
        "pull_request": subject.get("pull_request"),
        "base_commit": subject.get("base_commit"),
        "head_commit": subject.get("head_commit"),
        "changed_files": subject.get("changed_files"),
        "candidate_primary_content_sha256": subject.get("candidate_primary_content_sha256"),
        "exact_pr_bundle_hash": subject.get("exact_pr_bundle_hash"),
        "integration_head_subject_id": subject.get("integration_head_subject_id"),
    }
    if not _matching_exact_binding(normalized_subject, observation):
        raise ExternalPrReviewError("Builder evidence is not bound to the current exact PR head.")
    focused = checks.get("focused_build")
    forbidden = checks.get("forbidden_token_scan")
    diff_check = checks.get("diff_check")
    probes = checks.get("axiom_probes")
    worktree = checks.get("worktree")
    remote = checks.get("post_review_remote_refresh")
    if not all(isinstance(item, Mapping) for item in (focused, forbidden, diff_check, probes, worktree, remote)):
        raise ExternalPrReviewError("Builder evidence is missing a required exact-head check.")
    if int(focused.get("exit_code", -1)) != 0:
        raise ExternalPrReviewError("Focused exact-head build did not pass.")
    findings = forbidden.get("findings")
    if int(forbidden.get("exit_code", -1)) != 0 or not isinstance(findings, Mapping) or findings:
        raise ExternalPrReviewError("Forbidden-token scan did not pass cleanly.")
    if int(diff_check.get("exit_code", -1)) != 0:
        raise ExternalPrReviewError("Exact PR diff check did not pass.")
    declarations = probes.get("declarations")
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    if int(probes.get("exit_code", -1)) != 0 or not isinstance(declarations, Mapping) or not declarations:
        raise ExternalPrReviewError("Axiom probes are missing or failed.")
    for declaration, axioms in declarations.items():
        if not isinstance(axioms, list) or not set(map(str, axioms)).issubset(allowed_axioms):
            raise ExternalPrReviewError(f"Axiom probe for {declaration} contains unsupported dependencies.")
    if str(worktree.get("tracked_status", "") or "") != "clean" or str(
        worktree.get("head_commit", "") or ""
    ) != observation.head_sha:
        raise ExternalPrReviewError("Builder checkout was not clean at the exact reviewed head.")
    if (
        str(remote.get("state", "") or "").upper() != "OPEN"
        or remote.get("is_draft") is not True
        or str(remote.get("base_commit", "") or "") != observation.base_sha
        or str(remote.get("head_commit", "") or "") != observation.head_sha
        or list(remote.get("changed_files", [])) != list(observation.changed_files)
    ):
        raise ExternalPrReviewError("Builder post-review remote refresh does not match the current draft PR.")


def adopt_external_pr_evidence(
    *,
    settings,
    store: WorkspaceStateStore,
    repo: str,
    pr_number: int,
    task_id: str,
    review_path: Path,
    classification_path: Path,
    builder_path: Path,
    observer: Callable[[str, int, str], PullRequestObservation] = observe_pull_request,
) -> dict[str, Any]:
    """Apply a completed pre-CLI exact-head review without pretending it was a Toy review."""

    store.assert_integrity()
    canonical_task = canonicalize_block_id(task_id)
    observation = observer(repo, pr_number, canonical_task)
    _require_reviewable_pr(observation)
    if canonical_task != observation.subject.task_id:
        raise ExternalPrReviewError("Requested task does not match the exact PR subject.")

    review_path = review_path.expanduser().resolve()
    classification_path = classification_path.expanduser().resolve()
    builder_path = builder_path.expanduser().resolve()
    review = _json_object(review_path)
    classification = _json_object(classification_path)
    builder = _json_object(builder_path)
    _validate_builder_evidence(builder, observation)

    if str(review.get("schema_version", "") or "") != "toy-apollo.kenneth-pr-exact-semantic-review.v1":
        raise ExternalPrReviewError("Exact semantic review schema is not supported.")
    if canonicalize_block_id(str(review.get("task_id", "") or "")) != canonical_task:
        raise ExternalPrReviewError("Exact semantic review task does not match the PR subject.")
    if str(review.get("verdict", "") or "").lower() != "pass":
        raise ExternalPrReviewError("Only a passing exact semantic review can receive eligible coverage.")
    if str(review.get("review_subject_file", "") or "").replace("\\", "/") != observation.subject.primary_path:
        raise ExternalPrReviewError("Exact semantic review primary path does not match the PR subject.")
    if (
        str(review.get("candidate_hash", "") or "") != observation.subject.primary_hash
        or str(review.get("subject_bundle_hash", "") or "") != observation.subject.bundle_hash
    ):
        raise ExternalPrReviewError("Exact semantic review hashes do not match the PR subject.")
    review_binding = review.get("exact_binding")
    if not isinstance(review_binding, Mapping) or not _matching_exact_binding(review_binding, observation):
        raise ExternalPrReviewError("Exact semantic review binding does not match the current PR head.")
    independence = review.get("reviewer_independence")
    if not isinstance(independence, Mapping) or independence.get("read_only") is not True:
        raise ExternalPrReviewError("Exact semantic review lacks independent read-only attestation.")
    forbidden_independence = (
        "modified_candidate",
        "modified_evidence",
        "created_or_deleted_files",
        "git_checkout_commit_push_performed",
        "build_rerun_by_reviewer",
    )
    if any(independence.get(field) is not False for field in forbidden_independence):
        raise ExternalPrReviewError("Reviewer independence attestation permits a disallowed mutation.")
    questions = review.get("question_results")
    if not isinstance(questions, list) or not questions or any(
        not isinstance(item, Mapping) or str(item.get("status", "") or "").lower() != "pass"
        for item in questions
    ):
        raise ExternalPrReviewError("Exact semantic review did not pass every recorded review question.")

    if str(classification.get("schema_version", "") or "") != "toy-apollo.semantic-review-classification-supplement.v1":
        raise ExternalPrReviewError("Classification supplement schema is not supported.")
    if canonicalize_block_id(str(classification.get("task_id", "") or "")) != canonical_task:
        raise ExternalPrReviewError("Classification supplement task does not match the PR subject.")
    basis = classification.get("basis_review")
    classification_binding = classification.get("exact_binding")
    classification_independence = classification.get("reviewer_independence")
    if not isinstance(basis, Mapping) or sha256_file(review_path) != str(basis.get("sha256", "") or ""):
        raise ExternalPrReviewError("Classification supplement does not hash the supplied semantic review.")
    if not isinstance(classification_binding, Mapping) or not _matching_exact_binding(
        classification_binding, observation
    ):
        raise ExternalPrReviewError("Classification supplement binding does not match the current PR head.")
    if (
        not isinstance(classification_independence, Mapping)
        or classification_independence.get("read_only") is not True
        or classification_independence.get("lean_tokens_changed") is not False
        or classification_independence.get("modified_candidate_or_evidence") is not False
    ):
        raise ExternalPrReviewError("Classification supplement is not an unchanged read-only classification.")
    if str(classification.get("verdict", "") or "").lower() != "pass":
        raise ExternalPrReviewError("Classification supplement verdict is not pass.")
    proof_class = str(classification.get("proof_class", "") or "").strip()
    completion_class = str(classification.get("completion_class", "") or "").strip()

    from .core import open_runtime_ledger
    from .phase2_prompt_pack import resolve_phase2_task

    ledger = open_runtime_ledger(settings)
    task = resolve_phase2_task(canonical_task, ledger, settings)
    projection = classify_phase2_task_status(
        task_id=canonical_task,
        task_type=str(task.get("type", "") or ""),
        review_verdict="pass",
        proof_class=proof_class,
        completion_class=completion_class,
    )
    if projection.task_status != "pass":
        raise ExternalPrReviewError(
            f"Canonical classification does not project to pass: {projection.task_status}."
        )

    receipt_path = review_path.parent / "external_pr_review_apply_receipt.json"
    receipt = {
        "schema": "toy-apollo.external-pr-review-apply.v1",
        "task_id": canonical_task,
        "repo": observation.repo,
        "pr_number": observation.number,
        "base_sha": observation.base_sha,
        "head_sha": observation.head_sha,
        "head_repo": observation.head_repo,
        "head_ref": observation.head_ref,
        "url": observation.url,
        "changed_files": list(observation.changed_files),
        "subject_id": observation.subject.subject_id,
        "bundle_hash": observation.subject.bundle_hash,
        "primary_hash": observation.subject.primary_hash,
        "subject_bundle": _subject_payload(observation.subject),
        "semantic_review": {"path": str(review_path), "sha256": sha256_file(review_path)},
        "classification": {
            "path": str(classification_path),
            "sha256": sha256_file(classification_path),
            "proof_class": proof_class,
            "completion_class": completion_class,
        },
        "builder_evidence": {"path": str(builder_path), "sha256": sha256_file(builder_path)},
        "reviewer_independence": dict(independence),
        "authority_scope": "kenneth_pr_exact_head_review",
        "authority_eligible": True,
        "pr_mutated": False,
        "applied_at": utc_now(),
    }
    if receipt_path.is_file():
        existing = _json_object(receipt_path)
        for key, value in existing.items():
            if key == "applied_at":
                continue
            if key not in receipt or receipt[key] != value:
                raise ExternalPrReviewError(
                    f"Existing apply receipt is inconsistent at {key}: {receipt_path}"
                )
        receipt["applied_at"] = str(existing.get("applied_at", "") or receipt["applied_at"])
        if existing != receipt:
            _write_json(receipt_path, receipt)
        else:
            receipt = existing
    else:
        _write_json(receipt_path, receipt)

    store.upsert_subject(observation.subject)
    review_id = store.record_review(
        task_id=canonical_task,
        subject_id=observation.subject.subject_id,
        verdict="pass",
        proof_class=proof_class,
        completion_class=completion_class,
        phase2_status="pass",
        evidence_path=receipt_path,
        evidence_hash=sha256_file(receipt_path),
        reviewer_independence=json.dumps(dict(independence), ensure_ascii=False, sort_keys=True),
        authority_scope="kenneth_pr_exact_head_review",
        authority_eligible=True,
    )
    store.set_task_head(
        task_id=canonical_task,
        role="kenneth_pr_head",
        subject_id=observation.subject.subject_id,
        detail={
            "repo": repo,
            "pr_number": pr_number,
            "head_sha": observation.head_sha,
            "review_id": review_id,
            "adopted_evidence": True,
        },
    )
    store.record_run(
        task_id=canonical_task,
        operation="external_pr_review_adopt",
        status="completed",
        subject_id=observation.subject.subject_id,
        artifact_path=receipt_path,
        detail={"repo": repo, "pr_number": pr_number, "head_sha": observation.head_sha},
        completed_at=utc_now(),
    )
    return {
        "task_id": canonical_task,
        "repo": repo,
        "pr_number": pr_number,
        "head_sha": observation.head_sha,
        "subject_id": observation.subject.subject_id,
        "bundle_hash": observation.subject.bundle_hash,
        "review_id": review_id,
        "proof_class": proof_class,
        "completion_class": completion_class,
        "phase2_status": "pass",
        "exact_head_covered": True,
        "apply_receipt": str(receipt_path),
        "pr_mutated": False,
    }
