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

## Reference Cases

Use these as style references:

- [def_4_3_sup_inf.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\def_4_3_sup_inf.lean)
- [def_4_3_limsup_liminf.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\def_4_3_limsup_liminf.lean)
- [thm_4_7.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\thm_4_7.lean)
- [thm_4_8.lean](D:\Grad_Study\Practimum\Formalization\toy-apollo\ToyApollo\Output\thm_4_8.lean)
