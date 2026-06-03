from __future__ import annotations

from dataclasses import dataclass
from typing import Any


PHASE2_FAILURE_STREAK_LIMIT = 15
PHASE2_AUTO_LOOP_REVIEW_ROUNDS = 15
PHASE2_AUTO_LOOP_BUILD_ATTEMPTS_PER_REVIEW = 15
PHASE2_AUTO_LOOP_NONPROGRESS_LIMIT = 15

REVIEW_FAILURE_KINDS = {
    "semantic_review_fail",
    "semantic_review_failed",
    "semantic_review_inconclusive",
}

BUILD_FAILURE_KINDS = {
    "build_check_failure",
    "build_failed",
    "build_failure",
    "repl_failed",
    "temp_build_failed",
    "final_build_failed",
    "missing_target_declaration",
    "empty_candidate",
    "self_import",
    "undeclared_local_import",
    "theorem_declared_as_prop_def",
    "axiom_placeholder",
    "vacuous_candidate",
    "overspecialized_candidate",
    "reversed_example_logic",
    "example_wrapped_theorem",
    "weakened_statement",
    "missing_required_coverage",
    "missing_local_foundation_lemma",
    "missing_import",
    "unknown_identifier",
    "noncomputable_required",
    "type_mismatch",
    "contains_sorry",
}


@dataclass(frozen=True)
class Phase2FailureCounters:
    build_fail_counter: int = 0
    review_fail_counter: int = 0
    limit: int = PHASE2_FAILURE_STREAK_LIMIT

    @property
    def exhausted(self) -> bool:
        return self.build_fail_counter >= self.limit or self.review_fail_counter >= self.limit


def phase2_failure_counters_from_history(history: Any) -> Phase2FailureCounters:
    if not isinstance(history, dict):
        return Phase2FailureCounters()
    attempts = history.get("attempts", [])
    if not isinstance(attempts, list):
        return Phase2FailureCounters()
    return phase2_failure_counters_from_attempts(attempts)


def phase2_failure_counters_from_attempts(attempts: Any) -> Phase2FailureCounters:
    if not isinstance(attempts, list):
        return Phase2FailureCounters()

    build_fail_counter = _trailing_build_failures(attempts)
    review_fail_counter = 0
    for attempt in attempts:
        if not isinstance(attempt, dict):
            continue
        if _stage(attempt) != "semantic_review":
            continue
        if bool(attempt.get("success")):
            review_fail_counter = 0
            continue
        if _kind(attempt) in REVIEW_FAILURE_KINDS:
            review_fail_counter += 1
    return Phase2FailureCounters(
        build_fail_counter=build_fail_counter,
        review_fail_counter=review_fail_counter,
    )


def phase2_failure_counters_from_task(raw_task: dict[str, Any]) -> Phase2FailureCounters:
    explicit_build = _optional_int(raw_task.get("phase2_build_fail_counter", raw_task.get("build_fail_counter")))
    explicit_review = _optional_int(raw_task.get("phase2_review_fail_counter", raw_task.get("review_fail_counter")))
    if explicit_build is not None or explicit_review is not None:
        return Phase2FailureCounters(
            build_fail_counter=max(0, explicit_build or 0),
            review_fail_counter=max(0, explicit_review or 0),
        )

    attempts = raw_task.get("attempts")
    if attempts is None:
        history = raw_task.get("attempt_history")
        if isinstance(history, dict):
            attempts = history.get("attempts")
    if isinstance(attempts, list):
        return phase2_failure_counters_from_attempts(attempts)

    failure_events = raw_task.get("failure_events")
    if isinstance(failure_events, list):
        return _counters_from_failure_events(failure_events)

    return Phase2FailureCounters()


def _trailing_build_failures(attempts: list[Any]) -> int:
    count = 0
    for attempt in reversed(attempts):
        if not isinstance(attempt, dict):
            break
        if _stage(attempt) != "build":
            break
        if bool(attempt.get("success")):
            break
        count += 1
    return count


def _counters_from_failure_events(events: list[Any]) -> Phase2FailureCounters:
    build_fail_counter = 0
    review_fail_counter = 0
    for event in events:
        if not isinstance(event, dict):
            continue
        kind = _kind(event)
        if kind in BUILD_FAILURE_KINDS:
            build_fail_counter += 1
            continue
        if kind in REVIEW_FAILURE_KINDS:
            review_fail_counter += 1
    return Phase2FailureCounters(
        build_fail_counter=build_fail_counter,
        review_fail_counter=review_fail_counter,
    )


def _stage(event: dict[str, Any]) -> str:
    return str(event.get("stage", "") or "").strip().lower().replace("-", "_")


def _kind(event: dict[str, Any]) -> str:
    raw = event.get("primary_failure_kind", event.get("kind", ""))
    kind = str(raw or "").strip().lower().replace("-", "_").replace(" ", "_")
    aliases = {
        "build_check": "build_check_failure",
        "semantic_review": "semantic_review_fail",
        "review_fail": "semantic_review_fail",
        "review_inconclusive": "semantic_review_inconclusive",
    }
    return aliases.get(kind, kind)


def _optional_int(raw: Any) -> int | None:
    if raw is None or raw == "":
        return None
    try:
        return int(raw)
    except (TypeError, ValueError):
        return None
