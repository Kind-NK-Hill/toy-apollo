# Kenneth Theorem 1.1 and 1.4 Official Repair Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task. Independent semantic review uses a read-only reviewer agent as required by Phase 2.

**Goal:** Promote repaired Kenneth Theorems 1.4 and 1.1 into ToyApollo only after all three gates pass.

**Architecture:** Seed fresh Phase 2 candidates from Kenneth commit `1dc1b65`, preserve Kenneth proof bodies, repair only the reviewed statement/API defects, and land through fresh independent semantic review plus `review-apply`. The existing ToyApollo code is used only as a regression and local-lemma reference.

**Tech Stack:** Lean 4.31.0, Mathlib/Lake, ToyApollo Phase 2 CLI, PowerShell, Git.

---

### Task 1: Establish fresh campaign state and RED evidence

**Files:**
- Generate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/project_ledger.json`
- Generate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/phase2_prompt_packs/thm_1_4/*`
- Generate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/phase2_prompt_packs/thm_1_1/*`

- [ ] Set `TOY_APOLLO_RUNTIME_ROOT` to the ToyApollo worktree and `TOY_APOLLO_ARTIFACT_ROOT` to the fresh campaign.
- [ ] Run `python run_chapter.py --phase 2 --phase2-mode pack --tasks thm_1_4,thm_1_1`.
- [ ] Read both task JSON files, source TeX spans, dependency contexts, proof obligations, and ledger rows.
- [ ] Record the existing Kenneth `thm_1_4` semantic failure and direct Kenneth `thm_1_1` build failure as RED evidence.

### Task 2: Repair and land Kenneth Theorem 1.4

**Files:**
- Modify candidate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/phase2_prompt_packs/thm_1_4/draft.lean`
- Promote on pass: `ToyApollo/Output/thm_1_4.lean`

- [ ] Seed `draft.lean` from Kenneth `ProbabilityTheory/chapter_01/thm_1_4.lean`, changing only the module import prefix.
- [ ] Run build-check and confirm the source-faithfulness test fails while any global `Monotone alpha` premise remains.
- [ ] Change the four theorem/helper premises to `MonotoneOn alpha (Set.Icc a b)` and pass the interval premise directly into `SourceHypotheses`.
- [ ] Run `python run_chapter.py --phase 2 --phase2-mode build-check --tasks thm_1_4` until the candidate builds.
- [ ] Run direct regression builds for `ToyApollo.Output.def_1_3` and `ToyApollo.Output.def_1_4` against the candidate-compatible dependency surface.
- [ ] Generate `review-now --review-subject candidate`, delegate independent read-only review, and write the bound result JSON.
- [ ] Run `review-apply`; if it does not project to `phase2_status=pass`, resume `auto-loop` rather than promoting manually.

### Task 3: Reconcile the Kenneth Theorem 1.1 proof family

**Files:**
- Modify candidate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/phase2_prompt_packs/thm_1_1/draft.lean`
- Modify support candidates only as generated/declared by the Phase 2 pack.
- Promote on pass: `ToyApollo/Output/thm_1_1.lean` and mechanically necessary stable support files.

- [ ] Seed the parent and nine Kenneth `thm_1_1*` files from commit `1dc1b65`, translating import prefixes only.
- [ ] Run direct build to reproduce the `Partition.noConfusion`/missing `DarbouxRS` interface failure.
- [ ] Reconcile the proof family with the prioritized Kenneth Definition 1.2 contract: eliminate the root `Partition` collision, provide the expected partition/core interface, and use the correct Fin tag/index types without changing the finite-discontinuity proof route.
- [ ] Replace theorem-level global `Monotone alpha` with `MonotoneOn alpha (Icc a b)` and propagate the local premise through source hypotheses and support lemmas.
- [ ] Run build-check until the parent and every declared support module build.
- [ ] Run regression builds for `ToyApollo.Output.thm_1_2`, `ToyApollo.Output.thm_1_3`, `ToyApollo.Output.thm_1_4`, `ToyApollo.Output.def_1_3`, and `ToyApollo.Output.def_1_4`.
- [ ] Generate candidate review, delegate independent read-only review, and apply only a pass-compatible result.
- [ ] If review fails or is inconclusive, continue through `auto-loop` within its recorded budget and stop only on a documented Phase 2 stop condition.

### Task 4: Final three-gate verification and commit

**Files:**
- Verify: `ToyApollo/Output/thm_1_4.lean`
- Verify: `ToyApollo/Output/thm_1_1.lean`
- Verify: fresh campaign review/apply artifacts

- [ ] Run direct Lake builds for both repaired theorems and all listed regressions.
- [ ] Scan active files for `sorry`, `admit`, `axiom`, and `native_decide`.
- [ ] Run `#print axioms` for both public theorems and their major proof owners.
- [ ] Run `python tools/check_repo_hygiene.py` and confirm no unrelated tracked files changed.
- [ ] Confirm both fresh ledger rows have `phase2_status=pass`, valid independent reviewer evidence, and matching apply receipts.
- [ ] Commit only reviewed ToyApollo source/support changes and the design/plan; do not push or alter Kenneth remote.

