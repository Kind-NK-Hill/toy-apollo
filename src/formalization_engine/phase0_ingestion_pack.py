from __future__ import annotations

import json
import re
import shutil
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from .core.settings import Settings


PHASE0_FILES = (
    "source_info.json",
    "raw_pdf_extract.txt",
    "cleanup_rules.md",
    "operator_prompt.md",
    "draft_input.tex",
    "validation_report.json",
    "apply_report.md",
)

_OUTPUT_STEM_RE = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
_SUBSECTION_RE = re.compile(r"\\subsection\*?\{([^}]*)\}")


def write_phase0_pack(
    pdf_path: Path | str,
    page_range: str,
    output_stem: str,
    settings: Settings,
) -> Path:
    output_stem = _validate_output_stem(output_stem)
    start_page, end_page = _parse_page_range(page_range)
    pdf_path = Path(pdf_path)

    pack_dir = _pack_dir(output_stem, settings)
    pack_dir.mkdir(parents=True, exist_ok=True)

    raw_extract = _extract_pdf_pages(pdf_path, start_page, end_page)
    source_info = {
        "source_pdf": str(pdf_path),
        "page_range": {"start": start_page, "end": end_page},
        "output_stem": output_stem,
        "target_input_file": _target_input_path(output_stem, settings).as_posix(),
        "generated_at": datetime.now(UTC).isoformat(),
    }

    _write_text(pack_dir / "source_info.json", json.dumps(source_info, indent=2, ensure_ascii=False) + "\n")
    _write_text(pack_dir / "raw_pdf_extract.txt", raw_extract)
    _write_text(pack_dir / "cleanup_rules.md", _cleanup_rules(output_stem))
    _write_text(pack_dir / "operator_prompt.md", _operator_prompt(output_stem))

    draft_path = pack_dir / "draft_input.tex"
    if not draft_path.exists():
        draft_path.write_text("", encoding="utf-8")
    validation_report_path = pack_dir / "validation_report.json"
    if not validation_report_path.exists():
        _write_json(validation_report_path, _validation_report(output_stem, "not_run", []))
    apply_report_path = pack_dir / "apply_report.md"
    if not apply_report_path.exists():
        _write_text(apply_report_path, "# Phase 0 Apply Report\n\nStatus: not_applied\n")

    return pack_dir


def validate_phase0_pack(output_stem: str, settings: Settings) -> tuple[bool, str, dict[str, Any]]:
    output_stem = _validate_output_stem(output_stem)
    pack_dir = _pack_dir(output_stem, settings)
    draft_path = pack_dir / "draft_input.tex"
    findings: list[dict[str, str]] = []

    if not pack_dir.exists():
        report = _validation_report(output_stem, "fail", [{"code": "missing_pack", "message": f"Phase 0 pack not found: {pack_dir}"}])
        return False, f"Phase 0 validation failed for {output_stem}: pack not found.", report

    if not draft_path.exists():
        findings.append({"code": "missing_draft", "message": "draft_input.tex does not exist."})
        text = ""
    else:
        text = draft_path.read_text(encoding="utf-8")
        if not text.strip():
            findings.append({"code": "empty_draft", "message": "draft_input.tex is empty."})

    if text.strip():
        findings.extend(_validate_clean_tex_shape(text))

    status = "pass" if not findings else "fail"
    report = _validation_report(output_stem, status, findings)
    _write_json(pack_dir / "validation_report.json", report)

    if findings:
        detail = f"Phase 0 validation failed for {output_stem}: {len(findings)} finding(s)."
        return False, detail, report
    return True, f"Phase 0 validation passed for {output_stem}.", report


def apply_phase0_pack(output_stem: str, settings: Settings) -> tuple[bool, str, Path]:
    output_stem = _validate_output_stem(output_stem)
    success, detail, _report = validate_phase0_pack(output_stem, settings)
    target_path = _target_input_path(output_stem, settings)
    pack_dir = _pack_dir(output_stem, settings)
    apply_report_path = pack_dir / "apply_report.md"

    if not success:
        if pack_dir.exists():
            _write_text(
                apply_report_path,
                f"# Phase 0 Apply Report\n\nStatus: failed\n\n{detail}\n",
            )
        return False, detail, target_path

    draft_path = pack_dir / "draft_input.tex"
    target_path.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(draft_path, target_path)
    _write_text(
        apply_report_path,
        "\n".join(
            [
                "# Phase 0 Apply Report",
                "",
                "Status: applied",
                f"Source draft: `{draft_path}`",
                f"Target input: `{target_path}`",
                "",
            ]
        ),
    )
    return True, f"Phase 0 applied {output_stem} to {target_path}.", target_path


def _pack_dir(output_stem: str, settings: Settings) -> Path:
    root = settings.phase0_ingestion_packs_dir or (settings.artifact_root / "phase0_ingestion_packs")
    return root / output_stem


def _target_input_path(output_stem: str, settings: Settings) -> Path:
    return settings.runtime_root / "inputs" / f"{output_stem}.tex"


def _validate_output_stem(output_stem: str) -> str:
    output_stem = str(output_stem or "").strip()
    if not _OUTPUT_STEM_RE.fullmatch(output_stem):
        raise ValueError(
            "Invalid phase0 output stem. Use lowercase words/digits separated by hyphens, "
            "for example: chapter9-moments-mgf."
        )
    return output_stem


def _parse_page_range(page_range: str) -> tuple[int, int]:
    raw = str(page_range or "").strip()
    match = re.fullmatch(r"(\d+)(?:-(\d+))?", raw)
    if not match:
        raise ValueError("Page range must use physical PDF pages, for example: 157-160.")
    start_page = int(match.group(1))
    end_page = int(match.group(2) or match.group(1))
    if start_page < 1 or end_page < start_page:
        raise ValueError("Page range must be 1-based and inclusive with end >= start.")
    return start_page, end_page


def _extract_pdf_pages(pdf_path: Path, start_page: int, end_page: int) -> str:
    from pypdf import PdfReader

    reader = PdfReader(str(pdf_path))
    total_pages = len(reader.pages)
    if end_page > total_pages:
        raise ValueError(f"Page range {start_page}-{end_page} exceeds PDF length {total_pages}.")

    chunks: list[str] = []
    for page_number in range(start_page, end_page + 1):
        page = reader.pages[page_number - 1]
        text = page.extract_text() or ""
        chunks.append(f"--- PDF physical page {page_number} ---\n{text.strip()}\n")
    return "\n".join(chunks)


def _validate_clean_tex_shape(text: str) -> list[dict[str, str]]:
    findings: list[dict[str, str]] = []

    if not (re.search(r"\\section\*\{", text) or re.search(r"\\subsection\*\{", text)):
        findings.append({"code": "missing_section_heading", "message": "Use \\section* or \\subsection* headings."})

    source_unit_error = _source_unit_error(text)
    if source_unit_error:
        findings.append({"code": "multiple_source_units", "message": source_unit_error})

    if _has_pdf_noise(text):
        findings.append({"code": "pdf_noise", "message": "Draft still contains PDF extraction noise or publication boilerplate."})

    if re.search(r"(?m)^\s*\d{1,4}\s*$", text):
        findings.append({"code": "pdf_page_number", "message": "Remove naked PDF page numbers."})

    if re.search(r"(?m)^\s*De(?:fi|ﬁ)nition\s+\d", text) and r"\begin{defbox}" not in text:
        findings.append({"code": "definition_box", "message": "Definitions should use defbox environments."})

    if re.search(r"(?m)^\s*Theorem\s+\d", text) and r"\begin{thmbox}" not in text:
        findings.append({"code": "theorem_box", "message": "Theorems should use thmbox environments."})

    if re.search(r"(?m)^\s*Example\s+\d", text) and not re.search(r"\\textbf\{Example\s+[^}]+\}\s*\\\\", text):
        findings.append({"code": "example_format", "message": "Examples should use \\textbf{Example ...} \\\\."})

    return findings


def _source_unit_error(text: str) -> str:
    subsection_titles = [match.group(1).strip() for match in _SUBSECTION_RE.finditer(text)]
    numbered = [title for title in subsection_titles if re.match(r"^\d+\.\d+(?:\b|\s)", title)]
    problems = [title for title in subsection_titles if title.strip().lower() == "problems"]

    if len(numbered) > 1:
        return (
            "Use one source unit per cleaned input; found multiple numbered subsections: "
            + ", ".join(numbered)
        )
    if numbered and problems:
        return "Put Problems in a separate cleaned input from numbered textbook subsections."
    return ""


def _has_pdf_noise(text: str) -> bool:
    lowered = text.lower()
    noise_patterns = (
        "deﬁnition",
        "w eh a v e",
        ".e[",
        "doi.org",
        "copyright",
        "©",
        "the author(s)",
        "under exclusive license",
        "compact textbooks",
        "measure-theoretic probability",
    )
    if any(pattern in lowered for pattern in noise_patterns):
        return True
    if re.search(r"(?m)^\s*\d+\s+Moment Generating Functions\s*$", text):
        return True
    return text.count("|") >= 10


def _validation_report(output_stem: str, status: str, findings: list[dict[str, str]]) -> dict[str, Any]:
    return {
        "output_stem": output_stem,
        "status": status,
        "generated_at": datetime.now(UTC).isoformat(),
        "findings": findings,
    }


def _cleanup_rules(output_stem: str) -> str:
    return f"""# Phase 0 Cleanup Rules

Target output stem: `{output_stem}`

- Preserve textbook mathematical content and order.
- Remove PDF headers, footers, page numbers, DOI/copyright lines, and extraction artifacts.
- Use one source unit per cleaned input: one numbered subsection, or one Problems section.
- Chapter intro may be included only with the first subsection of that chapter.
- Use `\\section*{{...}}` for the chapter heading and `\\subsection*{{...}}` for the target section.
- Put definitions in `defbox` and theorems in `thmbox`.
- Format examples as `\\textbf{{Example ...}} \\\\`.
- Keep the result as clean TeX suitable for Phase 1. Do not include Phase 1 plans or ledger metadata.
"""


def _operator_prompt(output_stem: str) -> str:
    return f"""# Phase 0 Operator Prompt

Clean `raw_pdf_extract.txt` into `draft_input.tex` for `{output_stem}`.

Scope:
- Write only the textbook material intended for `inputs/{output_stem}.tex`.
- Write exactly one source unit: one numbered subsection, or one Problems section.
- Do not clean a whole chapter into a single input file.
- Do not include PDF boilerplate or OCR/extraction artifacts.
- Do not create a plan, update the ledger, or run Phase 1 from this pack.

After editing `draft_input.tex`, run:

```powershell
formalize --phase 0 --phase0-mode validate --phase0-output {output_stem}
formalize --phase 0 --phase0-mode apply --phase0-output {output_stem}
```
"""


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    _write_text(path, json.dumps(payload, indent=2, ensure_ascii=False) + "\n")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
