from __future__ import annotations

from pathlib import Path
from typing import Any


def build_legacy_intent_contract(task: dict[str, Any]) -> dict[str, Any]:
    from .phase2_prompt_pack import build_legacy_intent_contract as _impl

    return _impl(task)


def ensure_intent_contract(pack_dir: Path, task: dict[str, Any]) -> dict[str, Any]:
    from .phase2_prompt_pack import ensure_intent_contract as _impl

    return _impl(pack_dir, task)


def load_or_create_intent_contract(pack_dir: Path, task: dict[str, Any]) -> dict[str, Any]:
    from .phase2_prompt_pack import load_or_create_intent_contract as _impl

    return _impl(pack_dir, task)


def _prepare_existing_output_review_materials(*, task: dict[str, Any], ledger, settings, pack_dir: Path, output_path: Path, mode: str, build_output: str, force_new_attempt: bool = False) -> dict[str, Any]:
    from .phase2_prompt_pack import _prepare_existing_output_review_materials as _impl

    return _impl(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        output_path=output_path,
        mode=mode,
        build_output=build_output,
        force_new_attempt=force_new_attempt,
    )


def _write_codex_handoff_review_artifacts(*, task: dict[str, Any], ledger, settings, pack_dir: Path, attempt: int, candidate_path: Path, candidate_code: str, build_summary: dict[str, Any], mode: str = "review-pack", review_subject_kind: str = "candidate", build_result_file: str = "", build_candidate_file: str = "", build_candidate_hash: str = "") -> dict[str, Any]:
    from .phase2_prompt_pack import _write_codex_handoff_review_artifacts as _impl

    return _impl(
        task=task,
        ledger=ledger,
        settings=settings,
        pack_dir=pack_dir,
        attempt=attempt,
        candidate_path=candidate_path,
        candidate_code=candidate_code,
        build_summary=build_summary,
        mode=mode,
        review_subject_kind=review_subject_kind,
        build_result_file=build_result_file,
        build_candidate_file=build_candidate_file,
        build_candidate_hash=build_candidate_hash,
    )


async def write_codex_review_pack(task_id: str, ledger, settings, candidate_arg: str | None = None) -> tuple[bool, str]:
    from .phase2_prompt_pack import write_codex_review_pack as _impl

    return await _impl(task_id, ledger, settings, candidate_arg)


async def write_existing_output_review_pack(task_id: str, ledger, settings, *, force_new_attempt: bool = False) -> tuple[bool, str]:
    from .phase2_prompt_pack import write_existing_output_review_pack as _impl

    return await _impl(task_id, ledger, settings, force_new_attempt=force_new_attempt)


async def write_existing_support_review_pack(task_id: str, ledger, settings, *, force_new_attempt: bool = False) -> tuple[bool, str]:
    from .phase2_prompt_pack import write_existing_support_review_pack as _impl

    return await _impl(task_id, ledger, settings, force_new_attempt=force_new_attempt)


async def write_existing_output_review_queue(task_ids: list[str], ledger, settings) -> tuple[bool, str]:
    from .phase2_prompt_pack import write_existing_output_review_queue as _impl

    return await _impl(task_ids, ledger, settings)


def write_prompt_pack(task_id: str, ledger, settings, task: dict[str, Any] | None = None) -> Path:
    from .phase2_prompt_pack import write_prompt_pack as _impl

    return _impl(task_id, ledger, settings, task=task)


def hard_check_diagnostic(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _hard_check_diagnostic as _impl

    return _impl(*args, **kwargs)


def hard_dependency_proof_debt_blocker_message(task: dict[str, Any], ledger) -> str:
    from .phase2_prompt_pack import hard_dependency_proof_debt_blocker_message as _impl

    return _impl(task, ledger)


def parse_diagnostics(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _parse_diagnostics as _impl

    return _impl(*args, **kwargs)


def quarantine_official_outputs(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _quarantine_official_outputs as _impl

    return _impl(*args, **kwargs)


def record_semantic_review_attempt(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _record_semantic_review_attempt as _impl

    return _impl(*args, **kwargs)


def remove_symbols_owned_by_task(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _remove_symbols_owned_by_task as _impl

    return _impl(*args, **kwargs)


def review_diagnostics(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _review_diagnostics as _impl

    return _impl(*args, **kwargs)


def run_staged_official_build(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _run_staged_official_build as _impl

    return _impl(*args, **kwargs)


def run_official_module_build(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _run_official_module_build as _impl

    return _impl(*args, **kwargs)


def run_lean_module_build(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _run_lean_module_build as _impl

    return _impl(*args, **kwargs)


def support_review_target_from_obligations(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _support_review_target_from_obligations as _impl

    return _impl(*args, **kwargs)


def write_review_compat_summary(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _write_review_compat_summary as _impl

    return _impl(*args, **kwargs)


def ensure_task_registered(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import ensure_task_registered as _impl

    return _impl(*args, **kwargs)


def resolve_phase2_task(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import resolve_phase2_task as _impl

    return _impl(*args, **kwargs)


async def build_check_prompt_pack_candidate(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import build_check_prompt_pack_candidate as _impl

    return await _impl(*args, **kwargs)


def backfill_semantic_repair_history_from_request(*args: Any, **kwargs: Any):
    from .phase2_prompt_pack import _backfill_semantic_repair_history_from_request as _impl

    return _impl(*args, **kwargs)
