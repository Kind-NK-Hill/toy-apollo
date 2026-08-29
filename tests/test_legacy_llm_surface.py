import re
import sys
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


class LegacyLLMSurfaceTests(unittest.TestCase):
    LEGACY_DIRECT_GENERATION_FILES = [
        "src/agent.py",
        "src/deepseek_client.py",
        "src/architect.py",
        "src/parser.py",
        "src/textbook_parser.py",
        "src/orchestrator.py",
        "src/pipeline.py",
        "src/toy_apollo/pipeline/__init__.py",
        "src/toy_apollo/pipeline/architect.py",
        "src/toy_apollo/pipeline/auto_formalization.py",
        "src/toy_apollo/pipeline/orchestrator.py",
        "src/toy_apollo/pipeline/textbook_parser.py",
    ]

    ACTIVE_RUNTIME_ROOTS = [
        REPO_ROOT / "src",
        REPO_ROOT / "run_chapter.py",
        REPO_ROOT / "requirements.txt",
    ]

    EXCLUDED_PATH_PARTS = {
        "__pycache__",
        "backups",
    }

    BANNED_LITERALS = [
        "GeminiAgent",
        "DeepSeekClient",
        "TextbookOrchestrator",
        "AutoFormalizationPipeline",
        "--phase2-mode legacy",
        "phase2-mode legacy",
        "google.genai",
    ]

    BANNED_SECRET_PATTERNS = {
        "hardcoded_google_api_key": re.compile(r"AIza[0-9A-Za-z_\-]+"),
        "hardcoded_aristotle_api_key": re.compile(r"arstl_[0-9A-Za-z_\-]+"),
        "google_api_key_non_empty_default": re.compile(
            r"""os\.getenv\(\s*["']GOOGLE_API_KEY["']\s*,\s*["'][^"']+["']\s*\)"""
        ),
        "aristotle_api_key_non_empty_default": re.compile(
            r"""os\.getenv\(\s*["']ARISTOTLE_API_KEY["']\s*,\s*["'][^"']+["']\s*\)"""
        ),
        "gemini_3_hardcoded_default": re.compile(r"gemini-3"),
    }

    BANNED_IMPORT_PATTERNS = [
        re.compile(
            r"\bfrom\s+src\."
            r"(agent|deepseek_client|architect|parser|textbook_parser|orchestrator|pipeline)\b"
        ),
        re.compile(
            r"\bimport\s+src\."
            r"(agent|deepseek_client|architect|parser|textbook_parser|orchestrator|pipeline)\b"
        ),
    ]

    def _active_runtime_files(self) -> list[Path]:
        files: list[Path] = []
        for root in self.ACTIVE_RUNTIME_ROOTS:
            if root.is_file():
                files.append(root)
                continue
            if not root.exists():
                continue
            for path in root.rglob("*"):
                if not path.is_file():
                    continue
                if any(part in self.EXCLUDED_PATH_PARTS for part in path.relative_to(REPO_ROOT).parts):
                    continue
                if path.suffix not in {".py", ".txt"}:
                    continue
                files.append(path)
        return files

    def test_legacy_direct_generation_files_are_absent(self):
        existing = [path for path in self.LEGACY_DIRECT_GENERATION_FILES if (REPO_ROOT / path).exists()]
        self.assertEqual(existing, [])

    def test_active_runtime_does_not_reference_legacy_llm_pipeline(self):
        violations: list[str] = []
        for path in self._active_runtime_files():
            text = path.read_text(encoding="utf-8", errors="replace")
            rel = path.relative_to(REPO_ROOT).as_posix()
            for literal in self.BANNED_LITERALS:
                if literal in text:
                    violations.append(f"{rel}: contains {literal!r}")
            for name, pattern in self.BANNED_SECRET_PATTERNS.items():
                if pattern.search(text):
                    violations.append(f"{rel}: matches {name}")
            for pattern in self.BANNED_IMPORT_PATTERNS:
                if pattern.search(text):
                    violations.append(f"{rel}: matches {pattern.pattern!r}")
        self.assertEqual(violations, [])


if __name__ == "__main__":
    unittest.main()
