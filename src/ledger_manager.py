import copy
import hashlib
import json
import os
import re
import tempfile
import time
from datetime import datetime, timezone
from enum import Enum
from pathlib import Path
from typing import Any

from src.block_id_naming import (
    base_block_id,
    canonicalize_block_id,
    canonicalize_id_list,
    canonicalize_task_dict,
    is_derived_block_id,
    legacy_ids_for,
    normalize_legacy_id_list,
)


class TaskStatus(str, Enum):
    DISCOVERED = "DISCOVERED"          # Phase 1: Parsed
    LOCAL_FIXING = "LOCAL_FIXING"      # Phase 2: In progress
    PACKED = "PACKED"                  # Prompt pack prepared; awaiting operator/model candidate
    VERIFYING = "VERIFYING"            # Candidate is being locally verified
    FAILED_LOCAL = "FAILED_LOCAL"      # Phase 2: Failed locally
    OFFLOADED = "OFFLOADED"            # Legacy external-offload status; current Phase 3 does not emit it
    HARVESTED = "HARVESTED"            # Legacy external-result status; current Phase 3 does not emit it
    ALIGNING = "ALIGNING"              # Legacy Phase 4 status; current Phase 4 is disabled/no-op
    COMPLETED = "COMPLETED"            # Verified by lake build
    COMPLETED_WITH_PROOF_DEBT = "COMPLETED_WITH_PROOF_DEBT"  # Accepted with explicit proof-debt support
    USER_MODIFIED = "USER_MODIFIED"    # Output hash mismatch (User manual edit)
    ORPHANED = "ORPHANED"              # Task no longer in LaTeX source


class LedgerError(RuntimeError):
    pass


class LedgerSaveError(LedgerError):
    pass


class LedgerConcurrencyError(LedgerSaveError):
    pass


class LedgerDangerousStateError(LedgerSaveError):
    pass


class LedgerTaskNotFoundError(LedgerError):
    pass


class LedgerManager:
    def __init__(self, ledger_path="project_ledger.json"):
        self.ledger_path = Path(ledger_path)
        self.backup_path = self._default_backup_path(self.ledger_path)
        self.lock_path = self.ledger_path.with_name(f"{self.ledger_path.stem}.lock")
        self._loaded_snapshot_hash: str | None = None
        self._load_error: str = ""
        self.ledger = self._load_ledger()

    @staticmethod
    def _default_backup_path(ledger_path: Path) -> Path:
        suffix = ledger_path.suffix or ".json"
        return ledger_path.with_name(f"{ledger_path.stem}.backup{suffix}")

    @staticmethod
    def _now_iso() -> str:
        return datetime.now(timezone.utc).isoformat()

    @staticmethod
    def _version_hash(raw_bytes: bytes) -> str:
        return hashlib.sha256(raw_bytes).hexdigest()

    def _normalize_soft_imports(self, raw: object) -> list[str]:
        return canonicalize_id_list(raw)

    @staticmethod
    def _clone_ledger_data(data: dict[str, Any]) -> dict[str, Any]:
        return copy.deepcopy(data)

    def _is_ledger_empty(self, ledger: Any | None = None) -> bool:
        candidate = self.ledger if ledger is None else ledger
        if not isinstance(candidate, dict):
            return True
        tasks = candidate.get("tasks", {})
        symbols = candidate.get("symbols", {})
        task_count = len(tasks) if isinstance(tasks, dict) else 0
        symbol_count = len(symbols) if isinstance(symbols, dict) else 0
        return task_count == 0 and symbol_count == 0

    def _build_candidate_snapshot(
        self,
        task: dict,
        tid: str,
        soft_imports: list[str] | None = None,
    ) -> dict:
        task = canonicalize_task_dict(task)
        tid = canonicalize_block_id(tid)
        deps = task.get("dependencies", [])
        if not isinstance(deps, list):
            deps = []
        safe_deps = canonicalize_id_list(deps)
        if soft_imports is None:
            soft_imports = task.get("soft_imports", [])
        safe_soft_imports = self._normalize_soft_imports(soft_imports)

        depth_raw = task.get("depth", 0)
        depth = depth_raw if isinstance(depth_raw, int) else 0
        return {
            "block_id": tid,
            "type": task.get("type", "Problem"),
            "title": task.get("title", tid),
            "content": task.get("content", ""),
            "source_plan": task.get("source_plan", "unknown"),
            "dependencies": safe_deps,
            "soft_imports": safe_soft_imports,
            "depth": depth,
        }

    def _ensure_task_schema(self, task: dict, tid: str) -> None:
        tid = canonicalize_block_id(tid)
        task.setdefault("block_id", tid)
        task["block_id"] = canonicalize_block_id(task.get("block_id", tid)) or tid
        task.setdefault("canonical_block_id", task["block_id"])
        task["canonical_block_id"] = (
            canonicalize_block_id(task.get("canonical_block_id", task["block_id"]))
            or task["block_id"]
        )
        task.setdefault("type", "Problem")
        task.setdefault("title", tid)
        task.setdefault("input_hash", "")
        task.setdefault("status", TaskStatus.DISCOVERED.value)
        task.setdefault("source_plan", "unknown")
        task.setdefault("output_hash", None)
        task.setdefault("exported_symbols", [])
        task.setdefault("last_error", "")
        task.setdefault("phase3_attempts", 0)
        task.setdefault("phase4_attempts", 0)
        task.setdefault("last_offload_error", "")
        task.setdefault("last_align_error", "")
        task.setdefault("cloud_project_id", "")
        task.setdefault("last_offload_at", "")
        task.setdefault("last_harvest_at", "")
        task.setdefault("legacy_ids", [])
        if not isinstance(task["legacy_ids"], list):
            task["legacy_ids"] = []
        task["legacy_ids"] = normalize_legacy_id_list(
            task["legacy_ids"] + [task["block_id"]] + list(legacy_ids_for(task["block_id"]))
        )
        task.setdefault("last_pack_at", "")
        task.setdefault("last_verify_at", "")
        task.setdefault("pack_round", 0)
        task.setdefault("verify_attempts", 0)
        task.setdefault("build_attempts", 0)
        task.setdefault("latest_candidate_file", "")
        task.setdefault("latest_build_result_file", "")
        task.setdefault("latest_verify_result_file", "")
        task.setdefault("latest_semantic_review_input_file", "")
        task.setdefault("latest_semantic_review_result_file", "")
        task.setdefault("latest_semantic_review_report_file", "")
        task.setdefault("current_review_input_file", "")
        task.setdefault("current_review_prompt_file", "")
        task.setdefault("current_review_template_file", "")
        task.setdefault("current_review_subject_kind", "")
        task.setdefault("current_review_subject_file", "")
        task.setdefault("current_review_subject_hash", "")
        task.setdefault("current_review_origin", "")
        task.setdefault("latest_official_snapshot_file", "")
        task.setdefault("latest_operation_kind", "")
        task.setdefault("latest_operation_file", "")
        task.setdefault("pack_candidate_state", "draft")
        task.setdefault("latest_build_candidate_kind", "")
        task.setdefault("latest_build_candidate_file", "")
        task.setdefault("latest_build_candidate_hash", "")
        task.setdefault("latest_build_ready_candidate_kind", "")
        task.setdefault("latest_build_ready_candidate_file", "")
        task.setdefault("latest_build_ready_candidate_hash", "")
        task.setdefault("latest_search_manifest_file", "")
        task.setdefault("soft_imports_confirmed_at", "")
        task.setdefault("base_block_id", base_block_id(task["block_id"]) or task["block_id"])
        task["base_block_id"] = (
            base_block_id(task.get("base_block_id", task["block_id"]))
            or task["block_id"]
        )
        task.setdefault("parent_block_id", "")
        task.setdefault("is_derived", is_derived_block_id(task["block_id"]))
        task["is_derived"] = bool(task["is_derived"]) or is_derived_block_id(task["block_id"])

        snapshot = task.get("candidate_snapshot")
        if not isinstance(snapshot, dict):
            snapshot = {}
        snapshot.setdefault("block_id", task["block_id"])
        snapshot["block_id"] = (
            canonicalize_block_id(snapshot.get("block_id", task["block_id"]))
            or task["block_id"]
        )
        snapshot.setdefault("type", task.get("type", "Problem"))
        snapshot.setdefault("title", task.get("title", tid))
        snapshot.setdefault("content", "")
        snapshot.setdefault("source_plan", task.get("source_plan", "unknown"))
        deps = snapshot.get("dependencies", [])
        if not isinstance(deps, list):
            deps = []
        snapshot["dependencies"] = canonicalize_id_list(deps)
        snapshot["soft_imports"] = self._normalize_soft_imports(snapshot.get("soft_imports", []))
        depth_raw = snapshot.get("depth", 0)
        snapshot["depth"] = depth_raw if isinstance(depth_raw, int) else 0
        task["candidate_snapshot"] = snapshot

    def _migrate_loaded_ledger(self, data: dict) -> dict:
        tasks = data.get("tasks", {})
        migrated_tasks: dict[str, dict] = {}
        if isinstance(tasks, dict):
            for original_tid, task in tasks.items():
                if not isinstance(task, dict):
                    continue
                canonical_tid = canonicalize_block_id(original_tid)
                if not canonical_tid:
                    continue
                payload = dict(task)
                payload.setdefault("legacy_ids", [])
                payload["legacy_ids"] = normalize_legacy_id_list(
                    payload["legacy_ids"] + [original_tid] + list(legacy_ids_for(canonical_tid))
                )
                existing = migrated_tasks.get(canonical_tid)
                if existing is None:
                    migrated_tasks[canonical_tid] = payload
                else:
                    existing["legacy_ids"] = canonicalize_id_list(
                        existing.get("legacy_ids", []) + payload["legacy_ids"]
                    )
                    for field in ("type", "title", "input_hash", "status", "source_plan", "output_hash"):
                        if payload.get(field):
                            existing[field] = payload[field]
                    if payload.get("candidate_snapshot"):
                        existing["candidate_snapshot"] = payload["candidate_snapshot"]
                self._ensure_task_schema(migrated_tasks[canonical_tid], canonical_tid)
        data["tasks"] = migrated_tasks

        symbols = data.get("symbols", {})
        migrated_symbols: dict[str, str] = {}
        if isinstance(symbols, dict):
            for sym, task_id in symbols.items():
                if not isinstance(sym, str):
                    continue
                canonical_tid = canonicalize_block_id(str(task_id or ""))
                if canonical_tid:
                    migrated_symbols[sym] = canonical_tid
        data["symbols"] = migrated_symbols
        return data

    def _normalize_ledger_for_runtime(self) -> None:
        if not isinstance(self.ledger, dict):
            raise LedgerSaveError("Ledger root must be a JSON object.")
        if "symbols" not in self.ledger or not isinstance(self.ledger["symbols"], dict):
            self.ledger["symbols"] = {}
        if "tasks" not in self.ledger or not isinstance(self.ledger["tasks"], dict):
            self.ledger["tasks"] = {}
        self.ledger = self._migrate_loaded_ledger(self.ledger)

    def _read_snapshot(self, path: Path) -> dict[str, Any]:
        snapshot: dict[str, Any] = {
            "path": path,
            "exists": path.exists(),
            "raw_bytes": b"",
            "hash": None,
            "recoverable": False,
            "data": None,
            "empty": True,
            "error": "",
        }
        if not snapshot["exists"]:
            return snapshot

        try:
            raw_bytes = path.read_bytes()
        except Exception as exc:
            snapshot["error"] = str(exc)
            return snapshot

        snapshot["raw_bytes"] = raw_bytes
        snapshot["hash"] = self._version_hash(raw_bytes)
        if not raw_bytes:
            snapshot["error"] = "Ledger file is empty."
            return snapshot

        try:
            data = json.loads(raw_bytes.decode("utf-8"))
            if not isinstance(data, dict):
                raise ValueError("Ledger root must be a JSON object.")
            if "symbols" not in data:
                data["symbols"] = {}
            if "tasks" not in data or not isinstance(data["tasks"], dict):
                data["tasks"] = {}
            migrated = self._migrate_loaded_ledger(data)
            snapshot["data"] = migrated
            snapshot["recoverable"] = True
            snapshot["empty"] = self._is_ledger_empty(migrated)
        except Exception as exc:
            snapshot["error"] = str(exc)
        return snapshot

    def _load_ledger(self) -> dict:
        snapshot = self._read_snapshot(self.ledger_path)
        self._loaded_snapshot_hash = snapshot["hash"]
        if snapshot["recoverable"]:
            self._load_error = ""
            return snapshot["data"]
        if snapshot["exists"]:
            self._load_error = snapshot["error"] or "Ledger snapshot is unreadable."
            print(
                f"⚠️ Ledger load error: {self._load_error}. "
                "Loaded an empty in-memory ledger; recover_from_disk() before saving."
            )
        return {"tasks": {}, "symbols": {}}

    def _serialize_ledger(self) -> bytes:
        self._normalize_ledger_for_runtime()
        return json.dumps(self.ledger, indent=4, ensure_ascii=False).encode("utf-8")

    def _write_bytes_atomic(self, target: Path, raw_bytes: bytes) -> None:
        target.parent.mkdir(parents=True, exist_ok=True)
        temp_name = None
        try:
            with tempfile.NamedTemporaryFile(
                mode="wb",
                delete=False,
                dir=target.parent,
                prefix=f".{target.name}.",
                suffix=".tmp",
            ) as handle:
                temp_name = handle.name
                handle.write(raw_bytes)
                handle.flush()
                os.fsync(handle.fileno())
            os.replace(temp_name, target)
        except Exception:
            if temp_name and os.path.exists(temp_name):
                os.remove(temp_name)
            raise

    def _preserve_backup_before_write(self, current_snapshot: dict[str, Any]) -> None:
        if current_snapshot["recoverable"] and not current_snapshot["empty"]:
            self._write_bytes_atomic(self.backup_path, current_snapshot["raw_bytes"])

    def _assert_expected_version(self, current_snapshot: dict[str, Any]) -> None:
        if current_snapshot["hash"] != self._loaded_snapshot_hash:
            raise LedgerConcurrencyError(
                "Refusing to overwrite ledger because the on-disk version changed since load. "
                f"expected={self._loaded_snapshot_hash!r} current={current_snapshot['hash']!r}"
            )

    def _assert_safe_to_save(
        self,
        current_snapshot: dict[str, Any],
        *,
        force_empty_save: bool,
        ledger: Any | None = None,
        load_error: str | None = None,
    ) -> None:
        ledger_is_empty = self._is_ledger_empty(self.ledger if ledger is None else ledger)
        effective_load_error = self._load_error if load_error is None else load_error
        if effective_load_error:
            raise LedgerDangerousStateError(
                "Refusing to save because the ledger was loaded from unreadable disk data. "
                "Call recover_from_disk() or recover_from_backup() before saving."
            )
        if not ledger_is_empty:
            return
        if force_empty_save:
            return
        if current_snapshot["recoverable"] and not current_snapshot["empty"]:
            raise LedgerDangerousStateError(
                "Refusing to overwrite a non-empty disk ledger with an empty in-memory ledger. "
                "Use reset(write_to_disk=True) or save(force_empty_save=True) if this is intentional."
            )
        if current_snapshot["exists"] and not current_snapshot["recoverable"]:
            raise LedgerDangerousStateError(
                "Refusing to overwrite an unreadable on-disk ledger from an empty in-memory ledger. "
                "Recover first or use an explicit reset."
            )

    def _require_task(self, task_id: str) -> tuple[str, dict]:
        task_id = canonicalize_block_id(task_id)
        if not task_id:
            raise LedgerTaskNotFoundError("Task id is empty or invalid.")
        task = self.ledger.get("tasks", {}).get(task_id)
        if not isinstance(task, dict):
            raise LedgerTaskNotFoundError(f"Task {task_id!r} is not registered in the ledger.")
        self._ensure_task_schema(task, task_id)
        return task_id, task

    def _acquire_lock(
        self,
        *,
        timeout_seconds: float = 10.0,
        poll_interval: float = 0.05,
        stale_lock_seconds: float = 60.0,
    ) -> int:
        self.lock_path.parent.mkdir(parents=True, exist_ok=True)
        deadline = time.monotonic() + timeout_seconds
        while True:
            try:
                fd = os.open(self.lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                payload = f"pid={os.getpid()} created_at={self._now_iso()}\n".encode("utf-8")
                os.write(fd, payload)
                return fd
            except FileExistsError:
                try:
                    lock_age = time.time() - self.lock_path.stat().st_mtime
                except FileNotFoundError:
                    continue
                if lock_age >= stale_lock_seconds:
                    try:
                        os.remove(self.lock_path)
                        continue
                    except FileNotFoundError:
                        continue
                    except OSError:
                        pass
                if time.monotonic() >= deadline:
                    raise LedgerConcurrencyError(
                        f"Timed out waiting for ledger lock: {self.lock_path}"
                    )
                time.sleep(poll_interval)

    def _release_lock(self, fd: int | None) -> None:
        if fd is None:
            return
        try:
            os.close(fd)
        finally:
            try:
                os.remove(self.lock_path)
            except FileNotFoundError:
                pass

    def _transaction_base_ledger(self, current_snapshot: dict[str, Any], backup_snapshot: dict[str, Any]) -> dict[str, Any]:
        if current_snapshot["recoverable"]:
            return self._clone_ledger_data(current_snapshot["data"])
        if not current_snapshot["exists"]:
            return {"tasks": {}, "symbols": {}}
        if backup_snapshot["recoverable"]:
            return self._clone_ledger_data(backup_snapshot["data"])
        raise LedgerDangerousStateError(
            "Refusing to modify ledger because the on-disk ledger is unreadable and no recoverable backup exists."
        )

    def _run_transaction(self, mutator, *, force_empty_save: bool = False):
        lock_fd: int | None = None
        original_ledger = self.ledger
        original_hash = self._loaded_snapshot_hash
        original_load_error = self._load_error
        try:
            lock_fd = self._acquire_lock()
            current_snapshot = self._read_snapshot(self.ledger_path)
            backup_snapshot = self._read_snapshot(self.backup_path)
            self.ledger = self._transaction_base_ledger(current_snapshot, backup_snapshot)
            self._loaded_snapshot_hash = current_snapshot["hash"]
            self._load_error = ""
            result = mutator()
            raw_bytes = self._serialize_ledger()
            self._assert_safe_to_save(
                current_snapshot,
                force_empty_save=force_empty_save,
                ledger=self.ledger,
                load_error="",
            )
            self._preserve_backup_before_write(current_snapshot)
            self._write_bytes_atomic(self.ledger_path, raw_bytes)
            self._loaded_snapshot_hash = self._version_hash(raw_bytes)
            self._load_error = ""
            return result
        except Exception:
            self.ledger = original_ledger
            self._loaded_snapshot_hash = original_hash
            self._load_error = original_load_error
            raise
        finally:
            self._release_lock(lock_fd)

    def is_dangerous_empty_state(self) -> bool:
        if not self._is_ledger_empty():
            return False
        current_snapshot = self._read_snapshot(self.ledger_path)
        if current_snapshot["recoverable"] and not current_snapshot["empty"]:
            return True
        if current_snapshot["exists"] and not current_snapshot["recoverable"]:
            return True
        return False

    def has_recoverable_backup(self) -> bool:
        backup_snapshot = self._read_snapshot(self.backup_path)
        return bool(backup_snapshot["recoverable"] and not backup_snapshot["empty"])

    def recover_from_disk(self, *, prefer_backup: bool = False, allow_empty: bool = False) -> bool:
        primary_snapshot = self._read_snapshot(self.ledger_path)
        backup_snapshot = self._read_snapshot(self.backup_path)
        candidates = [backup_snapshot, primary_snapshot] if prefer_backup else [primary_snapshot, backup_snapshot]

        for snapshot in candidates:
            if not snapshot["recoverable"]:
                continue
            if snapshot["empty"] and not allow_empty:
                continue
            self.ledger = snapshot["data"]
            self._loaded_snapshot_hash = primary_snapshot["hash"]
            self._load_error = ""
            return True
        return False

    def recover_from_backup(self, *, allow_empty: bool = False) -> bool:
        return self.recover_from_disk(prefer_backup=True, allow_empty=allow_empty)

    def reset(self, *, write_to_disk: bool = False) -> None:
        self.ledger = {"tasks": {}, "symbols": {}}
        if write_to_disk:
            self.save(force_empty_save=True)

    def save(self, *, force_empty_save: bool = False) -> None:
        lock_fd: int | None = None
        try:
            lock_fd = self._acquire_lock()
            raw_bytes = self._serialize_ledger()
            current_snapshot = self._read_snapshot(self.ledger_path)
            self._assert_expected_version(current_snapshot)
            self._assert_safe_to_save(current_snapshot, force_empty_save=force_empty_save)
            self._preserve_backup_before_write(current_snapshot)
            self._write_bytes_atomic(self.ledger_path, raw_bytes)
            self._loaded_snapshot_hash = self._version_hash(raw_bytes)
            self._load_error = ""
        finally:
            self._release_lock(lock_fd)

    def _hash_text(self, content):
        if not content:
            return ""
        return hashlib.md5(content.encode("utf-8")).hexdigest()

    def add_or_update_task(self, task):
        """Phase 1 entry point. Handles task drift and re-runs."""
        task = canonicalize_task_dict(task)
        tid = task["block_id"]
        current_input_hash = self._hash_text(task["content"])
        def mutate() -> None:
            if tid not in self.ledger["tasks"]:
                self.ledger["tasks"][tid] = {
                    "block_id": tid,
                    "type": task.get("type"),
                    "title": task.get("title", ""),
                    "input_hash": current_input_hash,
                    "status": TaskStatus.DISCOVERED.value,
                    "source_plan": task.get("source_plan", "unknown"),
                    "output_hash": None,
                    "exported_symbols": [],
                    "last_error": "",
                    "phase3_attempts": 0,
                    "phase4_attempts": 0,
                    "last_offload_error": "",
                    "last_align_error": "",
                    "cloud_project_id": "",
                    "last_offload_at": "",
                    "last_harvest_at": "",
                    "last_pack_at": "",
                    "last_verify_at": "",
                    "pack_round": 0,
                    "verify_attempts": 0,
                    "latest_candidate_file": "",
                    "latest_verify_result_file": "",
                    "latest_search_manifest_file": "",
                    "soft_imports_confirmed_at": "",
                    "candidate_snapshot": self._build_candidate_snapshot(task, tid),
                    "canonical_block_id": tid,
                    "legacy_ids": normalize_legacy_id_list([tid] + list(legacy_ids_for(tid))),
                    "base_block_id": base_block_id(tid) or tid,
                    "parent_block_id": "",
                    "is_derived": is_derived_block_id(tid),
                }
                return

            existing = self.ledger["tasks"][tid]
            self._ensure_task_schema(existing, tid)
            plan_soft_imports = self._normalize_soft_imports(task.get("soft_imports", []))
            existing_soft_imports = self._normalize_soft_imports(
                existing.get("candidate_snapshot", {}).get("soft_imports", [])
            )
            if existing["input_hash"] != current_input_hash:
                print(f"🔔 Task {tid} requirement changed. Resetting status to DISCOVERED.")
                existing["input_hash"] = current_input_hash
                if existing["status"] == TaskStatus.COMPLETED.value:
                    existing["status"] = TaskStatus.DISCOVERED.value
                existing_soft_imports = []
                existing["soft_imports_confirmed_at"] = ""
            soft_imports_confirmed = bool(str(existing.get("soft_imports_confirmed_at", "") or "").strip())
            task_type = str(task.get("type", existing.get("type", "")) or "").strip().lower()
            if plan_soft_imports and (task_type != "problem" or not soft_imports_confirmed):
                existing_soft_imports = plan_soft_imports

            if existing["status"] == TaskStatus.ORPHANED.value:
                existing["status"] = TaskStatus.DISCOVERED.value

            existing["type"] = task.get("type", existing.get("type", "Problem"))
            existing["title"] = task.get("title", existing.get("title", tid))
            existing["source_plan"] = task.get("source_plan", existing.get("source_plan", "unknown"))
            existing["canonical_block_id"] = tid
            existing["legacy_ids"] = normalize_legacy_id_list(
                existing.get("legacy_ids", []) + [tid] + list(legacy_ids_for(tid))
            )
            existing["base_block_id"] = base_block_id(tid) or tid
            existing["is_derived"] = is_derived_block_id(tid)
            existing["candidate_snapshot"] = self._build_candidate_snapshot(
                task,
                tid,
                soft_imports=existing_soft_imports,
            )

        self._run_transaction(mutate)

    def update_status(self, task_id, status: TaskStatus, error=""):
        def mutate() -> None:
            _, task = self._require_task(task_id)
            task["status"] = status.value
            if error:
                task["last_error"] = error

        self._run_transaction(mutate)

    def update_runtime_metadata(self, task_id: str, **fields) -> None:
        def mutate() -> None:
            _, task = self._require_task(task_id)
            for k, v in fields.items():
                task[k] = v

        self._run_transaction(mutate)

    def update_candidate_soft_imports(self, task_id: str, soft_imports: list[str]) -> None:
        def mutate() -> None:
            _, task = self._require_task(task_id)
            task["candidate_snapshot"]["soft_imports"] = self._normalize_soft_imports(soft_imports)

        self._run_transaction(mutate)

    def has_confirmed_soft_imports(self, task_id: str) -> bool:
        task_id = canonicalize_block_id(task_id)
        task = self.ledger["tasks"].get(task_id)
        if not task:
            return False
        self._ensure_task_schema(task, task_id)
        confirmed_at = str(task.get("soft_imports_confirmed_at", "") or "").strip()
        return bool(confirmed_at)

    def mark_soft_imports_confirmed(self, task_id: str, soft_imports: list[str] | None = None) -> None:
        def mutate() -> None:
            _, task = self._require_task(task_id)
            if soft_imports is not None:
                task["candidate_snapshot"]["soft_imports"] = self._normalize_soft_imports(soft_imports)
            task["soft_imports_confirmed_at"] = self._now_iso()

        self._run_transaction(mutate)

    def increment_attempt(self, task_id: str, field: str) -> int:
        result: dict[str, int] = {"value": 0}

        def mutate() -> None:
            _, task = self._require_task(task_id)
            current = task.get(field, 0)
            if not isinstance(current, int):
                current = 0
            current += 1
            task[field] = current
            result["value"] = current

        self._run_transaction(mutate)
        return result["value"]

    def mark_offloaded(self, task_id: str) -> None:
        """Compatibility helper for legacy ledgers; current Phase 3 does not call this."""
        self.update_runtime_metadata(task_id, last_offload_at=self._now_iso())

    def mark_harvested(self, task_id: str, cloud_project_id: str | None = None) -> None:
        """Compatibility helper for legacy ledgers; current Phase 3 does not call this."""
        updates = {"last_harvest_at": self._now_iso()}
        if cloud_project_id:
            updates["cloud_project_id"] = cloud_project_id
        self.update_runtime_metadata(task_id, **updates)

    def mark_packed(
        self,
        task_id: str,
        *,
        pack_round: int,
        latest_candidate_file: str = "",
        latest_search_manifest_file: str = "",
    ) -> None:
        self.update_runtime_metadata(
            task_id,
            last_pack_at=self._now_iso(),
            pack_round=pack_round,
            latest_candidate_file=latest_candidate_file,
            latest_search_manifest_file=latest_search_manifest_file,
        )

    def mark_verifying(
        self,
        task_id: str,
        *,
        latest_candidate_file: str = "",
        latest_verify_result_file: str = "",
        verify_attempts: int | None = None,
    ) -> None:
        updates = {"last_verify_at": self._now_iso()}
        if latest_candidate_file:
            updates["latest_candidate_file"] = latest_candidate_file
        if latest_verify_result_file:
            updates["latest_verify_result_file"] = latest_verify_result_file
        if verify_attempts is not None:
            updates["verify_attempts"] = verify_attempts
        self.update_runtime_metadata(task_id, **updates)

    def get_tasks_by_status(self, statuses):
        status_values = [s.value for s in statuses]
        return [t for t in self.ledger["tasks"].values() if t["status"] in status_values]

    def _extract_symbols(self, lean_code):
        symbols = []
        matches = re.finditer(
            r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([a-zA-Z0-9_']+)",
            lean_code,
            re.MULTILINE,
        )
        for match in matches:
            symbols.append(match.group(1))
        return symbols

    def reconcile_file(self, task_id, file_path):
        """Audit logic: Matches disk file with ledger record."""
        task_id = canonicalize_block_id(task_id)
        p = Path(file_path)
        if not p.exists():
            return False

        with open(p, "r", encoding="utf-8") as f:
            content = f.read()

        current_output_hash = self._hash_text(content)
        task = self.ledger["tasks"].get(task_id)

        if not task:
            return False

        # Detect User Modification
        if task["output_hash"] and task["output_hash"] != current_output_hash:
            if task["status"] != TaskStatus.USER_MODIFIED.value:
                print(f"🛠️  Task {task_id} was manually modified by user.")
                self.update_status(task_id, TaskStatus.USER_MODIFIED)

        # Update symbols and hash for successful builds
        # (This is called after a successful 'lake build')
        return current_output_hash

    def register_success(self, task_id, lean_code, output_hash):
        def mutate() -> None:
            canonical_task_id, task = self._require_task(task_id)
            symbols = self._extract_symbols(lean_code)
            task["output_hash"] = output_hash
            task["exported_symbols"] = symbols
            task["status"] = TaskStatus.COMPLETED.value
            task["last_align_error"] = ""
            task["last_error"] = ""

            for sym, owner in list(self.ledger["symbols"].items()):
                if owner == canonical_task_id:
                    del self.ledger["symbols"][sym]
            for sym in symbols:
                self.ledger["symbols"][sym] = canonical_task_id

        self._run_transaction(mutate)

    def mark_orphans(self, currently_found_ids, source_plan: str = ""):
        """Mark tasks that are in ledger but no longer in the LaTeX source.

        When *source_plan* is given, only tasks whose ``source_plan`` field
        matches are considered.  This prevents a single-file Phase 1 apply
        from orphaning every task in unrelated chapters.
        """
        current_ids = set(canonicalize_id_list(currently_found_ids))

        def mutate() -> None:
            for tid, task in self.ledger["tasks"].items():
                if source_plan and task.get("source_plan", "") != source_plan:
                    continue
                if tid not in current_ids and task["status"] != TaskStatus.ORPHANED.value:
                    print(f"👻 Task {tid} is now an orphan (not found in source).")
                    task["status"] = TaskStatus.ORPHANED.value

        self._run_transaction(mutate)

    def remove_symbols_owned_by_task(self, task_id: str) -> None:
        def mutate() -> None:
            canonical_task_id = canonicalize_block_id(task_id)
            for symbol, owner in list(self.ledger.get("symbols", {}).items()):
                if owner == canonical_task_id:
                    del self.ledger["symbols"][symbol]

        self._run_transaction(mutate)

    def get_summary(self):
        stats = {s.value: 0 for s in TaskStatus}
        for t in self.ledger["tasks"].values():
            status = t.get("status", "")
            if status not in stats:
                stats[status] = 0
            stats[status] += 1
        return stats

    def get_proof_debt_summary(self):
        task_count = 0
        obligation_count = 0
        completed_hidden_task_count = 0
        for task in self.ledger["tasks"].values():
            proof_summary = task.get("proof_obligation_summary", {})
            status_counts = proof_summary.get("status_counts", {}) if isinstance(proof_summary, dict) else {}
            if not isinstance(status_counts, dict):
                continue
            try:
                accepted_count = int(status_counts.get("accepted_as_proof_debt", 0) or 0)
            except (TypeError, ValueError):
                accepted_count = 0
            if accepted_count <= 0:
                continue
            task_count += 1
            obligation_count += accepted_count
            if task.get("status", "") == TaskStatus.COMPLETED.value:
                completed_hidden_task_count += 1
        return {
            "task_count": task_count,
            "obligation_count": obligation_count,
            "completed_hidden_task_count": completed_hidden_task_count,
        }

    def print_status_summary(self):
        print("\n" + "=" * 40)
        print("📊 TOY APOLLO PROJECT LEDGER")
        print("=" * 40)
        stats = self.get_summary()
        for status, count in stats.items():
            if count > 0:
                print(f"  {status.ljust(15)} : {count}")
        proof_debt = self.get_proof_debt_summary()
        if proof_debt["task_count"] > 0:
            print(
                "  "
                + "ACCEPTED_PROOF_DEBT".ljust(25)
                + f" : {proof_debt['task_count']} tasks / {proof_debt['obligation_count']} obligations"
            )
            if proof_debt["completed_hidden_task_count"] > 0:
                print(
                    "  "
                    + "COMPLETED_WITH_HIDDEN_DEBT".ljust(25)
                    + f" : {proof_debt['completed_hidden_task_count']} tasks"
                )
        print("=" * 40)
