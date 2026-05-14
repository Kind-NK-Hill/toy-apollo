# Phase2 Inventory

## Purpose

This document records the historical `phase2` execution chain and the current prompt-pack surface. It is an inspection artifact, not a runtime contract. The old direct-generation/orchestrator chain has been removed from the active CLI.

Related operator documents:

- [Phase2 Prompt-Pack Workflow](D:\Grad_Study\Practimum\Formalization\toy-apollo\docs\phase2_prompt_pack_workflow.md)
- [Phase2 Candidate Guidelines](D:\Grad_Study\Practimum\Formalization\toy-apollo\docs\phase2_candidate_guidelines.md)
- [Chapter1/2 Cross-Chapter Dependency Rules](D:\Grad_Study\Practimum\Formalization\toy-apollo\docs\chapter1_2_cross_chapter_dependency.md)

## Prompt-Pack Phase2 Operator Path

The active codebase exposes an operator-driven Phase2 path in [src/toy_apollo/cli/app.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\cli\app.py):

- `pack`
- `build-check`
- `review-pack`
- `review-existing`
- `review-now`
- `review-fix`
- `auto-loop`
- `review-existing-queue`
- `review-apply`
- `verify`
- `audit`

Current responsibilities in that path:

- `review-pack`, `review-existing`, and `review-existing-queue` prepare reviewer materials and `semantic_review_request_vM.json`
- `review-now` is the Codex-facing orchestration entrypoint; runtime prepares the request and the current Codex agent writes `semantic_review_result_vM.json` / `semantic_review_report_vM.md`
- `auto-loop` is the same-session Codex orchestration entrypoint; runtime advances review/apply/repair/build transitions while the current Codex agent still performs the authoring edit and reviewer JSON write
- `review-apply` validates and consumes an already existing review result
- `review-fix` activates the semantic-repair build loop from the latest failed review by materializing `review_repair_request_vM.json`, safely reseeding `draft.lean`, and refreshing repair-mode operator context
- `review-existing-queue` scans `ToyApollo/Output/*.lean` and emits queue reports under `phase2_prompt_packs/_reports/`
- live `auto-loop` state is stored in ledger runtime metadata; `metadata.json`, `context.md`, `failure_summary.md`, and `operator_prompt.md` mirror it for inspection

## Runtime Entry Chain

Historical direct-generation `phase2` entry flow:

1. [run_chapter.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\run_chapter.py)
2. [src/toy_apollo/cli/app.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\cli\app.py) `main()` -> `process_target()`
3. historical `src/orchestrator.py` `TextbookOrchestrator.process_task_queue(...)` (removed from active code)
4. historical `src/pipeline.py` `AutoFormalizationPipeline.run_phase(...)` (removed from active code)

Role split:

- `run_chapter.py`: stable root entrypoint; inserts `src/` into `sys.path` and delegates to the package CLI.
- `app.py`: parses CLI arguments, resolves settings, creates directories, loads the ledger, and dispatches `phase2` on a plan file or a plan directory.
- `orchestrator.py`: owns the task queue, cache checks, decomposition, dependency context injection, success/failure bookkeeping, and output writes.
- `pipeline.py`: owns retrieval, prompt construction, model calls, REPL/build validation, retry loops, and rescue mode.

## Current Phase2 Data Flow

### Inputs and setup

- `phase2` input is a plan JSON file or a directory of plan JSON files.
- `step2_execute_plan(...)` reads the plan file and canonicalizes each task record.
- The CLI constructs a `TextbookOrchestrator` with:
  - `report_filename`
  - `output_dir`
  - `error_logs_dir`
  - `ledger`
  - fixed `max_depth=2`
- Runtime paths come from [src/toy_apollo/core/settings.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\core\settings.py). `TOY_APOLLO_ARTIFACT_ROOT` can relocate `plans/`, `reports/`, `output_lean_files/`, `error_logs/`, `formalized_chapters/`, and the ledger file without moving `ToyApollo/Output`.

### Orchestrator preprocessing

For each task in the queue, `TextbookOrchestrator.process_task_queue(...)`:

1. canonicalizes the queue and `root_task` links
2. registers all tasks in the ledger
3. derives `out_dir` and `err_dir` from `source_plan`
4. skips `Remark` tasks by emitting comment blocks only
5. runs `_check_cache(...)`

Cache behavior:

- If ledger says `COMPLETED` and the file hash still matches, the task is treated as cache-hit success.
- If a cached file exists and compiles via REPL/build checks, the task is reused.
- Dependency retrofitting may be attempted if cached code is missing required imports and the needed blocks already exist in `ContextManager.code_store`.

### Parent-task branching

For non-remark tasks that do not hit cache:

1. orchestrator sets ledger status to `LOCAL_FIXING`
2. it scans `out_dir` for existing derived files:
   - `block_id__lemma_*.lean`
   - `block_id_lemma_*.lean`
   - `block_id__main.lean`
   - `block_id_main.lean`
3. if any such files exist and the current task depth is `0`, the parent task is marked as `Decomposed` in the report and skipped

If no prior derived outputs short-circuit the task, the orchestrator assembles dependency context:

- explicit `import ToyApollo.Output.<dep>`
- failed theorem/definition signatures from `ContextManager.failed_statements`
- transitive dependency code from `ContextManager.get_context_for(...)`

### Decomposition decision

The orchestrator decomposes before direct formalization when:

- task content contains one of:
  - `tsum`
  - `algebra`
  - `measure`
  - `indicator`
  - `pairwise`
- or task content length is greater than `800`
- and task depth is below `max_depth`

When decomposition triggers:

1. `ProofArchitect.generate_plan(...)` is called
2. returned child tasks are normalized into canonical derived ids such as:
   - `parent__lemma_1`
   - `parent__main`
3. child dependency ids are rewritten through alias normalization
4. child tasks are inserted immediately after the parent task in the same queue
5. the parent task itself is logged as `Decomposed` and not directly formalized in that pass

If decomposition does not trigger, the task goes directly to `pipeline.run_phase(...)`.

### Pipeline execution

`AutoFormalizationPipeline.run_phase(...)` currently performs these stages:

1. reset model chat history
2. initialize `MathlibSearcher` if not already present
3. ask the agent for technical search probes via `generate_technical_queries(...)`
4. search Mathlib and local project context via `MathlibSearcher.search(...)`
5. rerank candidates with another external LLM call when enabled
6. REPL-verify candidate APIs via `MathlibSearcher.verify_candidates(...)`
7. inject formatted RAG context into agent chat history
8. prepend reflection notebook lessons if any exist
9. call the main model once for initial code generation
10. enter the guided retry loop
11. if guided retries exhaust, enter rescue mode

Guided retry loop:

- max attempts: `MAX_FAST_RETRIES = 15`
- each attempt sanitizes code, writes `ToyApollo/Output/Temp_Validation.lean`, and validates through REPL
- on repeated near-identical failures, the pipeline broadens search and reinjects alternative context
- each retry sleeps `15` seconds before the next model call

Rescue loop:

- starts with `Rewrite from scratch. No sorry.`
- max attempts: `MAX_DEEP_RETRIES = 5`
- validates with both `lake build` and REPL
- also sleeps `15` seconds between model calls

### Validation and write-back

If pipeline returns code:

1. orchestrator re-validates with REPL
2. if complete and sorry-free:
   - ledger registers success
   - `ContextManager` stores the code
   - code is written to:
     - `ToyApollo/Output/<block_id>.lean`
     - `output_lean_files/<plan_folder>/<block_id>.lean`
   - orchestrator runs `lake build ToyApollo.Output.<block_id>`
   - success is appended to the report and final chapter document
3. if validation fails:
   - ledger status becomes `FAILED_LOCAL`
   - a `sorry` stub is written to both output locations
   - failed signature/code is stored in `ContextManager.failed_statements`
   - the root task is appended to `unsolved_tasks`

If pipeline returns no code:

- ledger status becomes `FAILED_LOCAL`
- a `sorry` stub is still written
- the root task is appended to `unsolved_tasks`

### Materialized outputs

`phase2` can write to all of the following:

- `ToyApollo/Output/*.lean`
- `output_lean_files/<plan_folder>/*.lean`
- `reports/*_report.md`
- `error_logs/<plan_folder>/*_error.log`
- `formalized_chapters/*_Formalized.lean`
- `project_ledger.json`
- `lab_notebook.json`

## Support Components and Their Roles

### Entry and orchestration

| File | Called by | Phase2 role | Main outputs / side effects |
| --- | --- | --- | --- |
| [run_chapter.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\run_chapter.py) | shell / operator | Stable root entrypoint into package CLI | none beyond delegation |
| [src/toy_apollo/cli/app.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\cli\app.py) | `run_chapter.py` | Parses args, loads settings, dispatches prompt-pack modes | creates artifact directories, loads/saves ledger |
| historical `src/orchestrator.py` | removed | Queue execution, decomposition, cache use, context injection, write-back | no longer active |

### Model and prompt path

| File | Called by | Phase2 role | Main outputs / side effects |
| --- | --- | --- | --- |
| historical `src/pipeline.py` | removed | Retrieval + generation + validation loop | no longer active |
| historical `src/agent.py` | removed | Chat-history model wrapper | no longer active |
| historical `src/deepseek_client.py` | removed | Low-level external LLM transport | no longer active |
| historical `src/architect.py` | removed | Decomposes long tasks into derived sub-tasks | no longer active |

### Retrieval, context, and memory

| File | Called by | Phase2 role | Main outputs / side effects |
| --- | --- | --- | --- |
| [src/searcher.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\searcher.py) | prompt-pack utilities | FAISS search, local scan, candidate verification | loads embeddings/index; no external LLM rerank |
| [src/context_manager.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\context_manager.py) | `orchestrator.py` | Loads cached Lean blocks, resolves transitive dependencies, assembles reference context | in-memory `code_store` and `failed_statements` |
| [src/reflection.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\reflection.py) | `pipeline.py` | Supplies prior failure summaries back into prompts | reads/writes `lab_notebook.json` |
| [src/indexer.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\indexer.py) | `searcher.py` | FAISS index and corpus loader for Mathlib search | loads vector index and corpus files |

### Lean validation

| File | Called by | Phase2 role | Main outputs / side effects |
| --- | --- | --- | --- |
| [src/compiler.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\compiler.py) | prompt-pack validators, `searcher.py` | Writes temp validation file, runs `lake build`, runs REPL validation | `ToyApollo/Output/Temp_Validation.lean`, `.repl_tmp`, `lake exe repl` subprocesses |

### Configuration

| File | Called by | Phase2 role | Main outputs / side effects |
| --- | --- | --- | --- |
| [src/config.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\config.py) | active modules needing shared paths/API keys | Exposes path aliases and Aristotle key lookup | imports settings into module-level aliases |
| [src/toy_apollo/core/settings.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\core\settings.py) | `app.py`, `config.py` | Resolves runtime root vs artifact root and all artifact paths | changes where plans/reports/error logs/output dirs/ledger are read and written |

## Phase2 Status Semantics in Practice

Observed status behavior from the current implementation:

- `LOCAL_FIXING`: set by orchestrator before active local generation work starts
- `COMPLETED`: set when output hash is registered after successful validation
- `FAILED_LOCAL`: set when generation returns no code, returns code that still fails validation, or integration fails

Additional notes:

- `phase2` does not increment a dedicated `phase2_attempts` field in the current active path.
- `phase2` writes `sorry` stubs even when the failure happened after partial code generation.
- `phase2` can leave parent tasks in a practical `Decomposed` state in reports without a distinct persisted ledger status that means "waiting on child tasks."

## Current Failure Modes

These are current behaviors and risks, not proposed fixes.

1. Historical `phase2` had no `--tasks` execution granularity.
   - The old full-plan chain has been removed from active CLI routing.
   - The prompt-pack workflow is now the task-granular Phase 2 path.

2. Historical derived outputs short-circuit parent tasks.
   - Existing `_lemma_`, `__lemma_`, `_main`, or `__main` files in `output_lean_files/...` cause the parent task at depth `0` to be logged as `Decomposed` and skipped.
   - This makes rerunning a single parent task non-idempotent unless outputs are isolated or cleaned.

3. `ProofArchitect` decomposition can lead to unstable derived-task handling.
   - Child tasks are inserted into the live queue after normalization.
   - The observed `def_4_3_sup_inf` run showed repeated failures under the same derived id `def_4_3_sup_inf__main`, indicating that child identity or task-to-report alignment can collapse in practice.

4. Historical `run_phase(...)` was expensive and external-LLM-dependent.
   - One run can trigger:
     - technical query generation
     - reranking
     - main generation
     - many guided retries
     - rescue retries
   - Backoff and fixed sleeps make failures long-running and costly.

5. Output sanitization is not sufficient to guarantee Lean-only responses.
   - `_sanitize_code(...)` strips some fences and known summary markers.
   - It does not fully prevent explanatory prose, Markdown headings, or mixed natural-language blocks from surviving into Lean validation.

6. `Definition` tasks can collide with Mathlib names.
   - The system does not pre-check whether a requested object is already present in Mathlib before asking the model to define it.
   - The observed `def_4_3_sup_inf` failure included attempted redefinitions of `upperBounds` and `IsLUB`.

7. `MathlibSearcher` adds startup and rerank cost even when the real task is local repair or direct formalization.
   - It loads FAISS state when available.
   - It can also trigger a `SentenceTransformer` load path in surrounding infrastructure.
   - This adds overhead before any meaningful proof progress is made.

8. Failure write-back is lossy.
   - On failure, orchestrator writes a generic `sorry` stub over task outputs.
   - This can discard partially useful generated code from the active output location while leaving only logs as the detailed record.

## Observed Failure Example: `def_4_3_sup_inf`

The isolated run under:

- `D:\Grad_Study\Practimum\Formalization\toy-apollo\_tmp_phase2_artifacts_def_4_3_sup_inf`

showed the current system behavior clearly:

- parent task `def_4_3_sup_inf` was logged as `Decomposed`
- child attempts repeatedly failed
- the report recorded multiple failures under `def_4_3_sup_inf__main`
- the error log contained mixed Lean code plus natural-language explanations and Markdown-style sections
- the temporary output file ended as:
  - `import Mathlib`
  - `theorem def_4_3_sup_inf__main : sorry := by sorry`

Artifacts:

- [report](D:\Grad_Study\Practimum\Formalization\toy-apollo\_tmp_phase2_artifacts_def_4_3_sup_inf\reports\_tmp_phase2_def_4_3_sup_inf_report.md)
- [error log](D:\Grad_Study\Practimum\Formalization\toy-apollo\_tmp_phase2_artifacts_def_4_3_sup_inf\error_logs\10_chap4_operations\def_4_3_sup_inf__main_error.log)
- [generated output](D:\Grad_Study\Practimum\Formalization\toy-apollo\_tmp_phase2_artifacts_def_4_3_sup_inf\output_lean_files\10_chap4_operations\def_4_3_sup_inf__main.lean)

This example is consistent with the failure modes above and should be treated as representative of the current pipeline shape.

## Tracked Files

This is the working refactor inventory for `phase2`.

| File | Subsystem | Phase2 role | Must keep | Refactor outlook |
| --- | --- | --- | --- | --- |
| [run_chapter.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\run_chapter.py) | entrypoint | shell entry into package CLI | yes | keep |
| [src/toy_apollo/cli/app.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\cli\app.py) | CLI dispatch | launches prompt-pack modes and resolves artifact paths | yes | keep |
| historical `src/orchestrator.py` | task orchestration | queue execution, decomposition branch, write-back, ledger updates | removed | archive only |
| historical `src/pipeline.py` | generation pipeline | retrieval/generation/validation/retry core | removed | archive only |
| historical `src/agent.py` | model wrapper | chat history, tech query generation, feedback prompts | removed | archive only |
| historical `src/deepseek_client.py` | API client | raw external LLM transport | removed | archive only |
| historical `src/architect.py` | decomposition | converts long tasks into derived sub-tasks | removed | archive only |
| [src/searcher.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\searcher.py) | retrieval | search and candidate verification | conditional | keep without external LLM rerank |
| [src/context_manager.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\context_manager.py) | context cache | loads prior Lean code and assembles task context | yes | keep |
| [src/reflection.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\reflection.py) | memory | injects prior failure lessons | no | retire |
| [src/indexer.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\indexer.py) | FAISS support | vector index load/search support | conditional | keep |
| [src/compiler.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\compiler.py) | Lean validation | REPL and `lake build` execution | yes | keep |
| [src/config.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\config.py) | shared config | path aliases and Aristotle key lookup | yes | keep small |
| [src/toy_apollo/core/settings.py](D:\Grad_Study\Practimum\Formalization\toy-apollo\src\toy_apollo\core\settings.py) | path settings | runtime/artifact path resolution | yes | keep |

## Codex-First Architecture Note

The current refactor direction is no longer "replace the old loop with another internal loop".

The new `phase2` keeps the valuable historical mechanisms:

- local Mathlib search
- local dependency reuse
- local REPL / `lake build` validation
- failure memory across attempts

But these mechanisms are redistributed into Codex-facing subsystems:

- grounding:
  - `search_manifest.json`
  - `search_notes.md`
  - verified local `#check` evidence
- memory:
  - `attempt_history.json`
  - `failure_summary.md`
  - append-only `candidate_vN.lean` and `verify_result_vN.json`
- verification:
  - temporary module validation
  - final promotion gate

The strategy layer is intentionally moved out of the repo and into Codex.

That means:

- repo code should expose evidence, diagnostics, and history
- Codex should decide whether to patch, rewrite, or change direction
- `legacy` is no longer an active Phase 2 CLI mode.
