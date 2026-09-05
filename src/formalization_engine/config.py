import os
from formalization_engine.core.settings import get_settings

GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY", "").strip()
MODEL_NAME = os.getenv("MODEL_NAME", "").strip()
ARCHITECT_MODEL_NAME = os.getenv("ARCHITECT_MODEL_NAME", "").strip()

_settings = get_settings()
PROJECT_ROOT = str(_settings.runtime_root)
MATHLIB_PATH = str(_settings.mathlib_path)
OUTPUT_LEAN_DIR = str(_settings.output_lean_files_dir)
REPORTS_DIR = str(_settings.reports_dir)
FORMALIZED_CHAPTERS_DIR = str(_settings.formalized_chapters_dir)
ERROR_LOGS_DIR = str(_settings.error_logs_dir)
PROJECT_LEDGER_PATH = str(_settings.project_ledger_file)
LAB_NOTEBOOK_PATH = str(_settings.lab_notebook_file)

MAX_FAST_RETRIES = 15
MAX_DEEP_RETRIES = 5

ARISTOTLE_API_KEY = os.getenv("ARISTOTLE_API_KEY", "").strip()

