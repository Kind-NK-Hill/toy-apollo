import os
import json
import hashlib
import re
from enum import Enum
from pathlib import Path

class TaskStatus(str, Enum):
    DISCOVERED = "DISCOVERED"          # Phase 1: Parsed
    LOCAL_FIXING = "LOCAL_FIXING"      # Phase 2: In progress
    FAILED_LOCAL = "FAILED_LOCAL"      # Phase 2: Failed locally
    OFFLOADED = "OFFLOADED"            # Phase 3: Sent to Aristotle
    HARVESTED = "HARVESTED"            # Phase 3: Result received
    ALIGNING = "ALIGNING"              # Phase 4: Fixing version/conflicts
    COMPLETED = "COMPLETED"            # Verified by lake build
    USER_MODIFIED = "USER_MODIFIED"    # Output hash mismatch (User manual edit)
    ORPHANED = "ORPHANED"              # Task no longer in LaTeX source

class LedgerManager:
    def __init__(self, ledger_path="project_ledger.json"):
        self.ledger_path = Path(ledger_path)
        self.ledger = self._load_ledger()
        
    def _load_ledger(self):
        if self.ledger_path.exists():
            try:
                with open(self.ledger_path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                    # Migration: Ensure symbols key exists
                    if "symbols" not in data: data["symbols"] = {}
                    return data
            except Exception as e:
                print(f"⚠️ Ledger load error: {e}. Starting fresh.")
        return {"tasks": {}, "symbols": {}}

    def save(self):
        with open(self.ledger_path, "w", encoding="utf-8") as f:
            json.dump(self.ledger, f, indent=4, ensure_ascii=False)

    def _hash_text(self, content):
        if not content: return ""
        return hashlib.md5(content.encode('utf-8')).hexdigest()

    def add_or_update_task(self, task):
        """Phase 1 entry point. Handles task drift and re-runs."""
        tid = task['block_id']
        current_input_hash = self._hash_text(task['content'])
        
        if tid not in self.ledger["tasks"]:
            # New task discovered
            self.ledger["tasks"][tid] = {
                "block_id": tid,
                "type": task.get("type"),
                "title": task.get("title", ""),
                "input_hash": current_input_hash,
                "status": TaskStatus.DISCOVERED.value,
                "source_plan": task.get("source_plan", "unknown"),
                "output_hash": None,
                "exported_symbols": [],
                "last_error": ""
            }
        else:
            # Existing task: Check for requirement changes
            existing = self.ledger["tasks"][tid]
            if existing["input_hash"] != current_input_hash:
                print(f"🔔 Task {tid} requirement changed. Resetting status to DISCOVERED.")
                existing["input_hash"] = current_input_hash
                if existing["status"] == TaskStatus.COMPLETED.value:
                    existing["status"] = TaskStatus.DISCOVERED.value # Needs re-verification
            
            # If it was orphaned, bring it back
            if existing["status"] == TaskStatus.ORPHANED.value:
                existing["status"] = TaskStatus.DISCOVERED.value

    def update_status(self, task_id, status: TaskStatus, error=""):
        if task_id in self.ledger["tasks"]:
            self.ledger["tasks"][task_id]["status"] = status.value
            if error:
                self.ledger["tasks"][task_id]["last_error"] = error
            self.save()

    def get_tasks_by_status(self, statuses):
        status_values = [s.value for s in statuses]
        return [t for t in self.ledger["tasks"].values() if t["status"] in status_values]

    def _extract_symbols(self, lean_code):
        symbols = []
        matches = re.finditer(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([a-zA-Z0-9_']+)", lean_code, re.MULTILINE)
        for match in matches:
            symbols.append(match.group(1))
        return symbols

    def reconcile_file(self, task_id, file_path):
        """Audit logic: Matches disk file with ledger record."""
        p = Path(file_path)
        if not p.exists(): return False
        
        with open(p, "r", encoding="utf-8") as f:
            content = f.read()
            
        current_output_hash = self._hash_text(content)
        task = self.ledger["tasks"].get(task_id)
        
        if not task: return False

        # Detect User Modification
        if task["output_hash"] and task["output_hash"] != current_output_hash:
            if task["status"] != TaskStatus.USER_MODIFIED.value:
                print(f"🛠️  Task {task_id} was manually modified by user.")
                self.update_status(task_id, TaskStatus.USER_MODIFIED)
        
        # Update symbols and hash for successful builds
        # (This is called after a successful 'lake build')
        return current_output_hash

    def register_success(self, task_id, lean_code, output_hash):
        if task_id in self.ledger["tasks"]:
            symbols = self._extract_symbols(lean_code)
            self.ledger["tasks"][task_id]["output_hash"] = output_hash
            self.ledger["tasks"][task_id]["exported_symbols"] = symbols
            self.ledger["tasks"][task_id]["status"] = TaskStatus.COMPLETED.value
            
            for sym in symbols:
                self.ledger["symbols"][sym] = task_id
            self.save()

    def mark_orphans(self, currently_found_ids):
        """Mark tasks that are in ledger but no longer in the LaTeX source."""
        for tid, task in self.ledger["tasks"].items():
            if tid not in currently_found_ids and task["status"] != TaskStatus.ORPHANED.value:
                print(f"👻 Task {tid} is now an orphan (not found in source).")
                task["status"] = TaskStatus.ORPHANED.value
        self.save()

    def get_summary(self):
        stats = {s.value: 0 for s in TaskStatus}
        for t in self.ledger["tasks"].values():
            stats[t["status"]] += 1
        return stats

    def print_status_summary(self):
        print("\n" + "="*40)
        print("📊 TOY APOLLO PROJECT LEDGER")
        print("="*40)
        stats = self.get_summary()
        for status, count in stats.items():
            if count > 0:
                print(f"  {status.ljust(15)} : {count}")
        print("="*40)
