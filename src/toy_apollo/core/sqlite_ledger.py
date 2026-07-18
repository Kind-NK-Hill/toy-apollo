from __future__ import annotations

import copy
import hashlib
from pathlib import Path
from typing import Any

from src.ledger_manager import (
    LedgerConcurrencyError,
    LedgerDangerousStateError,
    LedgerManager,
)

from ..state_store import StateConcurrencyError, WorkspaceStateStore, canonical_state_path


def campaign_id_for_artifact_root(artifact_root: Path) -> str:
    resolved = str(artifact_root.expanduser().resolve())
    digest = hashlib.sha256(resolved.lower().encode("utf-8")).hexdigest()[:16]
    return f"artifact-root:{digest}"


class SQLiteLedgerManager(LedgerManager):
    """Compatibility interface backed by the workspace SQLite store.

    Phase code still consumes ``ledger.ledger`` and the existing LedgerManager
    methods. Production writes are serialized into ``campaign_ledgers`` inside
    the one workspace database. A legacy JSON file is imported once when no
    SQLite campaign row exists, then left untouched as historical evidence.
    """

    def __init__(
        self,
        *,
        state_store: WorkspaceStateStore,
        artifact_root: Path,
        legacy_ledger_path: Path,
        campaign_id: str = "",
    ) -> None:
        self.state_store = state_store
        self.artifact_root = artifact_root.expanduser().resolve()
        self.campaign_id = campaign_id or campaign_id_for_artifact_root(self.artifact_root)
        self._db_revision: int | None = None

        # The parent loader supplies schema migration and conservative recovery
        # for a legacy file. It does not write during construction.
        super().__init__(ledger_path=str(legacy_ledger_path))
        legacy_ledger = copy.deepcopy(self.ledger)
        legacy_load_error = self._load_error

        if legacy_load_error:
            raise LedgerDangerousStateError(
                "Refusing to initialize SQLite state from an unreadable legacy ledger. "
                "Run the explicit state rebuild/recovery path first."
            )
        if not self.state_store.exists and not self.ledger_path.is_file():
            raise LedgerDangerousStateError(
                "Workspace state is missing and no legacy ledger is available for a safe import. "
                "Run 'python run_chapter.py state rebuild' before an operational phase command."
            )

        self.state_store.initialize()
        stored = self.state_store.load_campaign_ledger(self.campaign_id)
        if stored is not None:
            payload, revision = stored
            self.ledger = self._migrate_loaded_ledger(payload)
            self._db_revision = revision
            self._load_error = ""
            return

        self.ledger = self._migrate_loaded_ledger(legacy_ledger)
        self._db_revision = self.state_store.import_campaign_ledger(
            campaign_id=self.campaign_id,
            artifact_root=self.artifact_root,
            ledger=self.ledger,
            legacy_ledger_path=self.ledger_path,
            imported_from=str(self.ledger_path) if self.ledger_path.is_file() else "",
        )
        self._load_error = ""

    def _run_transaction(self, mutator, *, force_empty_save: bool = False):
        original_ledger = self.ledger
        original_revision = self._db_revision

        def mutate(base: dict[str, Any]):
            self.ledger = self._migrate_loaded_ledger(base)
            result = mutator()
            self._normalize_ledger_for_runtime()
            if self._is_ledger_empty() and not force_empty_save and not self._is_ledger_empty(base):
                raise LedgerDangerousStateError(
                    "Refusing to replace a non-empty SQLite campaign ledger with an empty ledger."
                )
            return result

        try:
            ledger, revision, result = self.state_store.mutate_campaign_ledger(
                campaign_id=self.campaign_id,
                artifact_root=self.artifact_root,
                legacy_ledger_path=self.ledger_path,
                mutator=mutate,
            )
            self.ledger = self._migrate_loaded_ledger(ledger)
            self._db_revision = revision
            self._load_error = ""
            return result
        except Exception:
            self.ledger = original_ledger
            self._db_revision = original_revision
            raise

    def save(self, *, force_empty_save: bool = False) -> None:
        self._normalize_ledger_for_runtime()
        if self._is_ledger_empty() and not force_empty_save:
            stored = self.state_store.load_campaign_ledger(self.campaign_id)
            if stored is not None and not self._is_ledger_empty(stored[0]):
                raise LedgerDangerousStateError(
                    "Refusing to overwrite a non-empty SQLite campaign ledger with an empty ledger."
                )
        try:
            self._db_revision = self.state_store.save_campaign_ledger(
                campaign_id=self.campaign_id,
                artifact_root=self.artifact_root,
                ledger=self.ledger,
                expected_revision=self._db_revision,
                legacy_ledger_path=self.ledger_path,
            )
        except StateConcurrencyError as exc:
            raise LedgerConcurrencyError(str(exc)) from exc

    def is_dangerous_empty_state(self) -> bool:
        if not self._is_ledger_empty():
            return False
        stored = self.state_store.load_campaign_ledger(self.campaign_id)
        return bool(stored is not None and not self._is_ledger_empty(stored[0]))

    def has_recoverable_backup(self) -> bool:
        # The workspace database is transactionally consistent. Explicit
        # database backups/rebuild replace per-campaign JSON backup semantics.
        return False

    def recover_from_disk(self, *, prefer_backup: bool = False, allow_empty: bool = False) -> bool:
        del prefer_backup
        stored = self.state_store.load_campaign_ledger(self.campaign_id)
        if stored is None:
            return False
        payload, revision = stored
        if self._is_ledger_empty(payload) and not allow_empty:
            return False
        self.ledger = self._migrate_loaded_ledger(payload)
        self._db_revision = revision
        self._load_error = ""
        return True

    def recover_from_backup(self, *, allow_empty: bool = False) -> bool:
        del allow_empty
        return False


def open_runtime_ledger(settings) -> SQLiteLedgerManager:
    state_path = Path(settings.state_db_file or canonical_state_path(settings.runtime_root))
    store = WorkspaceStateStore(state_path)
    store.validate_canonical_path(
        state_path,
        runtime_root=Path(settings.runtime_root),
        artifact_root=Path(settings.artifact_root),
    )
    return SQLiteLedgerManager(
        state_store=store,
        artifact_root=Path(settings.artifact_root),
        legacy_ledger_path=Path(settings.project_ledger_file),
        campaign_id="workspace:active",
    )
