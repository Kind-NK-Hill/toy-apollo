# ProbabilityTheoryFormalization

**AI Agent Workflows & Verification**

A research project that uses a probability textbook to develop AI-assisted code
generation, checking, review, and repair. The goal is to make generated Lean
code match the intended mathematics and remain usable by the modules that depend
on it.

**中文概述**：以概率论教材为场景，研究和开发 AI 辅助代码生成、自动检查、独立审查与迭代修复流程，保留可追溯的失败和修复记录。[阅读中文版](README.zh-CN.md)

**Shuo Deng:** workflow engineering and formalization, with AI assistance; first
author of the linked preprint. **Stack:** Python · Lean 4 · SQLite · automated verification.

[Paper](https://arxiv.org/abs/2607.27298) ·
[Two representative cases](#two-representative-cases) ·
[Merged collaboration](https://github.com/wkshum/ProbabilityTheory/pull/8) ·
[Contact](mailto:kdsdengshuo2823@gmail.com)

## My role and contributions

I am **Shuo Deng**, the developer of this workflow and a contributor to the
textbook formalization. My work covers:

- **Workflow design and implementation:** organize textbook passages into tasks,
  coordinate code generation and checks, and support iterative repair and
  recovery from interrupted work. [Workflow and architecture](docs/architecture.md)
- **Verification and state management:** bind reviews to the code and
  dependencies actually checked; retain build and repair records; use SQLite
  to track state and prevent outdated reviews from approving changed code.
  [State and evidence model](docs/workspace_state.md)
- **Failure analysis and research:** investigate missing assumptions, changed
  theorem interfaces, and broken downstream use; contribute reviewed fixes
  and coauthor the probability-formalization preprint.
  [Cases](examples/case-studies/) · [Merged fixes](https://github.com/wkshum/ProbabilityTheory/pull/7)

**Collaboration and AI assistance.** Kenneth W. Shum is the textbook author and
paper coauthor, and maintains the [collaborating textbook repository](https://github.com/wkshum/ProbabilityTheory).
My role centers on the workflow and formalization development; source corrections
are discussed with the textbook author. AI tools assist with code generation,
proof search, repairs, review, and documentation. These artifacts are not a claim
of wholly handwritten work; mathematical interpretation still requires human judgment.

## Outputs you can inspect

| Output | Evidence |
| --- | --- |
| **First-author preprint** | [*From Lecture Notes to Lean: Formalizing a Textbook on Probability Theory*](https://arxiv.org/abs/2607.27298) — **Shuo Deng**, Kenneth W. Shum. **arXiv preprint**, July 2026. |
| **Public system and cases** | [Workflow implementation](src/toy_apollo/) and [eight selected cases](examples/case-studies/), with code comparisons and review timelines. |
| **Merged collaboration** | [Chapter 2: align assumptions and interfaces](https://github.com/wkshum/ProbabilityTheory/pull/7) and [Chapter 3: refactor measure extension](https://github.com/wkshum/ProbabilityTheory/pull/8), both merged into Kenneth's repository. |

Review-history evaluation is ongoing: current analysis examines review consistency
and repair trajectories; final evaluation results are not yet reported here.

## Two representative cases

### Catch code that compiles but omits a required condition

**Problem:** a definition intended for probability measures accepted arbitrary
measures, allowing misleading values outside the intended domain.
**Action:** review identified the missing conditions; repair added explicit
probability-measure requirements and updated affected callers.
**Result:** the corrected definition and its downstream use received a fresh
passing review. Both the initial and final code compile.

[Code and review history](examples/case-studies/def_8_5/) ·
[Before](examples/case-studies/def_8_5/initial.lean) ·
[After](examples/case-studies/def_8_5/final.lean)

### Repair a module, then check and repair its downstream callers

**Problem:** a theorem compiled by taking its missing proof as an input.
Replacing that input with an internal proof still left a caller using the old interface.
**Action:** implement the proof, add the interface needed by the caller, and
migrate the caller through another review cycle.
**Result:** a fresh review accepted the repaired theorem and downstream migration.

[Case and timeline](examples/case-studies/thm_14_8/) ·
[Full proof](ToyApollo/Output/thm_14_8.lean)

The second case's short before/after files are **reduced interface demonstrations**;
the full mathematical proof is linked separately. All eight cases are selected
examples, **not an accuracy, cost, or productivity benchmark**.

![A real review sequence: compiling code, missing conditions, caller migration, and a fresh passing review](docs/images/def85-review.svg)

*Based on the [first case's retained review timeline](examples/case-studies/def_8_5/review-timeline.json);
the code lines are excerpts from its public snapshots.*

## Technical reading

The system checks compilation, reviews the intended meaning independently, then
accepts changes only while the reviewed code and dependencies remain current.
Model-assisted review is evidence, not a guarantee of mathematical correctness.

- [Architecture and workflow](docs/architecture.md)
- [Installation and verification commands](docs/development.md)
- [All eight cases and reproduction commands](examples/case-studies/)
- [Review criteria](docs/phase2/review_criteria.md) and [status contract](docs/phase2/status_contract.md)
- [Research context, related work, and limits](docs/project_notes.md)
- [Repository scope and publication history](docs/repository_scope.md)
- [Contributing](CONTRIBUTING.md) · [Security](SECURITY.md) · [MIT License](LICENSE)

The project was formerly called **ToyApollo**; existing code identifiers retain
that name for compatibility. Use **ProbabilityTheoryFormalization** when citing
the project.
