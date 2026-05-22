# Phase2 Candidate Guidelines

## Purpose

This document defines the candidate-writing rules for the prompt-pack workflow. It is narrower than the workflow runbook: this file is about how to write the Lean candidate itself.

## Core Principle

The candidate should create the smallest stable Lean artifact that captures the task's mathematical role and supports downstream dependencies.

Do not try to formalize every sentence of the textbook passage.

Textbook TeX fidelity has higher priority than minimizing local proof effort. If the source task is proof-heavy, construction-heavy, or counterexample-heavy, preserve the proof spine of the textbook argument instead of replacing it with an abstract wrapper that merely implies the final statement.

## Hard Rules

1. No `sorry`.
2. No Markdown.
3. No prose outside Lean comments or docstrings.
4. Do not redefine standard Mathlib objects that already exist.
5. Do not edit dependency files when working on the current task.
6. Use the imports provided by the pack unless there is a clear, necessary correction.
7. For `Problem` tasks, treat stored `soft imports` as mandatory imports, not optional hints.
8. Stay in the build loop until `build-check` passes; semantic review happens only after the candidate is technically runnable.
9. For proof-bearing tasks, inspect the original `inputs/<source>.tex` proof or solution span before writing or judging the candidate; prompt-pack mirrors are not a substitute for the source file.

## Preferred Construction Order

When writing a candidate, prefer this order:

1. direct reuse of Mathlib objects
2. direct reuse of `ToyApollo.Output.*` objects
3. small abbreviations or wrappers around existing objects
4. a short theorem/proof specialized to the task
5. only then a custom definition or proof

## Normal vs Complex Tasks

Before authoring a proof-bearing task, classify it as `normal` or `complex`.
This is a structural classification, not a list of favored theorem names.

Phase2 tracking has three levels:

- Level 0, ordinary Phase2: the default path. The candidate must build and pass
  semantic review, but the runtime does not create a new task-local
  `proof_obligations.json`.
- Level 1, interface translation: use theorem-level lemmas to translate between
  textbook notation and Mathlib or existing ToyApollo interfaces. This is not
  proof debt.
- Level 2, complex obligation tracking: create or maintain
  `proof_obligations.json` only when the task has independently reviewable
  proof steps that need explicit tracking.

Use `complex` when a one-piece proof would hide independent work that a reviewer
should be able to inspect separately. Common structural triggers are:

- the source proof has two or more nontrivial intermediate obligations
- the exported statement needs a chain of local helper lemmas before assembly
- existing local or Mathlib results almost match but require interface
  conversion before they can support the textbook claim
- the task has substantial hard dependencies or direct downstream consumers that
  will rely on the exact exported interface
- the source-to-Lean gap involves a construction, reduction, limiting passage,
  algebraic transformation, case split, or other proof operation that cannot be
  justified by pointing to a single existing theorem
- previous build/review attempts show repeated semantic non-progress rather than
  a small local syntax or type error

Use `normal` only when the task is a direct definition, wrapper, calculation, or
one-step theorem reuse and a reviewer can identify the source obligation and
Lean landing place without a helper chain.

Normal tasks should stay on the older Phase2 path: buildable Lean plus semantic
review of source claims, proof spine, interface contract, and downstream
adequacy. If an existing normal prompt pack already has
`phase2_prompt_packs/<task_id>/proof_obligations.json`, treat it as lightweight
metadata, not as a reason to introduce proof-debt scaffolding.

For a `complex` task, `proof_obligations.json` is the task-local
proof-obligation ledger. Split the source proof into obligation nodes, give each
node a source reference, dependencies, expected Lean landing place, and status,
then build the candidate as a reconstruction of those nodes. The exported
declaration should assemble proved obligations into the textbook claim; it must
not assume the hard obligations as theorem-level hypotheses.

This public-surface rule applies to all official task outputs, not only theorem
source blocks. Examples, problems, and definition-adjacent proof artifacts must
satisfy the same discipline when they export a theorem or task-facing helper.
For Chapter 10 and later, the only permitted standing proof-debt exception is
`thm_14_8_ProofBeyondBook`, because the source explicitly declares that proof
beyond the book. Ordinary `Support` and `Spine` packages must be replaced by
theorem-level evidence and internally assembled before a task is called clean.

A theorem or lemma that proves and returns a `Support`/`Spine` package is
allowed, and may be a useful internal assembly step. A public declaration must
not require such a package as a parameter unless it is the explicit
`thm_14_8_ProofBeyondBook` exception. A helper that consumes a support package
only to assemble the final task theorem should usually be `private` unless it is
a genuine reusable theorem whose premises are part of the textbook interface.

The generated `source_proof_spine` node is an unresolved placeholder, not a
completed decomposition. Replace it with concrete source-step nodes before
requesting semantic pass or declaring any terminal blocker.

`decomposition_plan.md` may still be used as a human-readable narrative, but the
machine-checked review basis is `proof_obligations.json`. Keep both in sync when
both exist.

Before creating new helper obligations, scan `ToyApollo/Output`, the live
ledger, dependency decisions, the relevant plan file, and Mathlib for existing
declarations that already cover the source proof step. The output scan must
include older textbook tasks outside the current chapter, definition files,
bridge/foundation files, renamed helper variants, and files imported by
downstream tasks. If such an output exists, use it or add it as a hard
dependency before continuing. A missing ledger record for an existing, buildable
output is a metadata repair, not evidence that the dependency is unavailable.

Scaffold hypotheses must be classified precisely:

- `interface_translation`: allowed temporarily only for representation or
  notation mismatch, and it must point to the obligation it helps discharge
- `assembly_scaffold`: an internal proof-organization object used while
  reconstructing the theorem; it must not become a public final-theorem
  hypothesis
- `support_constructor`: a theorem or lemma that proves and returns a
  `Support`/`Spine` package from theorem-level evidence
- `support_package`: a proved internal package used to assemble fields after
  the fields themselves have theorem-level landings
- `proof_debt_support`: an explicit, auditable support assumption for reusable
  mathematics not yet available locally or in Mathlib; it must name the source
  obligation it supports and must not be reported as a fully closed proof
- `proof_obligation`: a real source step that must become a ledger node and be
  proved or blocked explicitly
- `external_theorem_gap`: a possible local/Mathlib dependency that must be
  searched and either reused, imported, or ruled out
- `forbidden_shortcut`: an assumption of the main conclusion, a theorem-specific
  black box, or a hypothesis that erases a source proof step; this cannot pass
  semantic review

Use `interface_translation` lemmas for interface mismatch only. Do not use a
translation predicate to assume substantive source mathematics or the main
theorem conclusion. If the project explicitly accepts temporary support
assumptions, classify them as `proof_debt_support` instead and keep them
auditable. This is an exceptional cleanup mechanism, not the default authoring
mode for normal tasks. When review intentionally accepts such an item, record
the proof obligation status as `accepted_as_proof_debt`; this means the file is
buildable and the debt is explicit, not that the underlying reusable mathematics
has been fully proved. A task with accepted proof debt is not a clean upstream
dependency: downstream hard dependents and selected soft imports must wait
until `debt-fix` discharges the debt and the task lands without
`accepted_as_proof_debt`.
Do not mark a `proof_debt_support` item as `proved` merely because the candidate
defines a support structure or a source-spine field. The landing for `proved`
must be a theorem/lemma proving the source obligation, not a field projection
such as `SomeSourceSpine.some_field`.

## Definitions

For `Definition` tasks:

Prefer:

- `abbrev`
- short `def`
- reusable wrapper names

Avoid:

- shadowing Mathlib names
- long proofs inside a definition task unless they are unavoidable
- textbook commentary without exported declarations

Good pattern:

```lean
abbrev IsSupremum (A : Set ℝ) (r : ℝ) : Prop := IsLUB A r
```

## Theorems

For `Theorem` tasks:

Prefer:

- a concise, reusable theorem statement
- direct use of existing results such as `Measurable.iSup`
- proofs that are short and robust under version drift
- theorem structure that still follows the source TeX when the textbook proof carries essential mathematical content

Avoid:

- re-proving large theorems already in Mathlib
- overly decorative tactic scripts
- changing the theorem statement just to make the proof easier
- replacing the textbook proof with theorem-specific axiom packages, placeholder fields, or contradiction assumptions that erase the source argument

For proof-heavy theorems:

- keep the same mathematical assumptions that appear in the source
- preserve the main construction / partition / reduction steps from the source proof
- use local helper lemmas to organize the proof, but keep them inside the task unless a true reusable dependency is needed
- do not compress a long source proof into a vacuous impossibility shell

Before classifying a proof-heavy theorem as blocked, write down the source proof
spine from the original TeX and identify which step has no faithful Lean landing
place. A long proof, a missing one-shot Mathlib theorem, or an inconvenient first
draft is not by itself a hard failure.

For complex proof-heavy theorems, the source proof spine note must be upgraded
to a decomposition/reconstruction plan. If the task was previously hard-stopped
without such a plan, keep working until completion, explicit user interruption,
a documented mechanism blocker, or one of the two Phase 2 counters reaches 15:
`phase2_build_fail_counter` for consecutive failed `build-check` attempts, or
`phase2_review_fail_counter` for failed/inconclusive reviews of build-ready
candidates. Build failures and review failures do not add together; the task
fails only when one counter independently reaches 15.
Do not count a candidate as source-faithful if it replaces an existing local
output theorem with a fresh black-box assumption or translation.

## Examples

For `Example` tasks:

Prefer:

- formalizing the central mathematical conclusion
- one theorem or example statement that downstream tasks can reference
- preserving the source construction when the example is really a worked argument rather than a standalone conclusion

Avoid:

- encoding narrative exposition literally
- treating the example as pure prose
- dropping the source construction and keeping only a thin wrapper theorem when the textbook example depends on the construction itself

## Reuse of Local Dependencies

If a dependency is already completed:

- import it
- use its exported symbols
- do not copy its body into the current file

This rule is especially important for theorem tasks. If a previous definition already captures the right concept, the current file should consume it, not restate it.

For `Problem` tasks, the same rule applies to both:

- hard dependencies from the plan
- soft imports selected earlier and written into the ledger

Once a soft import appears in the pack, it is part of the mandatory import union.

## Problem Tasks

For `Problem` tasks:

Prefer:

- using the stored soft imports as the first project-local search space
- selecting the smallest stable formal statement that solves the mathematical core
- leveraging chapter-local `def/thm` materials before inventing new wrappers

Avoid:

- ignoring a preselected soft import because the statement looks solvable without it
- rebuilding the soft-dependency selection inside the candidate
- importing unrelated chapter materials that were not part of the final union

## Search Notes Usage

`search_notes.md` is advisory but should strongly shape the candidate.

Use it to confirm:

1. the real theorem or definition name
2. the import path
3. the actual `#check` signature

Do not guess names if `search_notes.md` or a direct local search can settle them.

## Candidate Size

Smaller is usually better.

A good candidate:

- compiles
- exports meaningful declarations
- is reusable by later tasks
- does not add unnecessary surface area

## Handling Noncomputability

If the candidate depends on noncomputable objects:

- mark the relevant `def` as `noncomputable`
- do not fight the system by forcing a computable definition where Mathlib already treats it as noncomputable

## Handling Build Warnings

Warnings are not all equal.

Acceptable:

- style/docstring warnings
- whitespace/linter warnings

Not acceptable:

- build failures
- bad imports
- unknown identifiers
- unresolved elaboration errors
- `sorry`

## Required Loop

Before asking for semantic review:

1. edit `draft.lean`
2. run `build-check`
3. inspect `build_result_vN.json`, `build_feedback.txt`, and `failure_summary.md`
4. edit again if needed
5. only once `build-check` succeeds, run `review-now --review-subject candidate`

Do not use `review-pack` as a substitute for the build loop.
`review-pack` only prepares compatibility handoff materials; it does not replace semantic review.

## Before Submitting a Candidate

Check:

1. does the file have a real top-level declaration?
2. does it reuse existing objects instead of redefining them?
3. is the declaration useful to downstream tasks?
4. would a fresh reader understand why this declaration exists?
5. has the current draft already passed `build-check`?
6. if the source TeX contains a substantial proof or construction, does the candidate still reflect that proof spine rather than hiding it behind placeholders or theorem-specific assumptions?
7. for proof-bearing tasks, did you inspect the original `inputs/<source>.tex` span rather than only `task.json` or `context.md`?
8. if this is complex, does `proof_obligations.json` contain concrete obligation nodes and does the candidate reconstruct them?

## Reference Cases

Use these as style references:

- [def_4_3_sup_inf.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\def_4_3_sup_inf.lean)
- [def_4_3_limsup_liminf.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\def_4_3_limsup_liminf.lean)
- [thm_4_7.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\thm_4_7.lean)
- [thm_4_8.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\thm_4_8.lean)
