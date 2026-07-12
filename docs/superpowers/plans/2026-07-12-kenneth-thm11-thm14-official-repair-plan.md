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
- [ ] Persist the existing Kenneth `thm_1_4` semantic failure and direct Kenneth `thm_1_1` build failure under the fresh campaign, including commit, command, exit code, and error/source-mismatch summary.

### Task 2: Repair and land Kenneth Theorem 1.4

**Files:**
- Modify first: `../_review-worktrees/kenneth-ProbabilityTheory-1dc1b65-thm1_2/ProbabilityTheory/chapter_01/thm_1_4.lean`
- Modify candidate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/phase2_prompt_packs/thm_1_4/draft.lean`
- Promote on pass: `ToyApollo/Output/thm_1_4.lean`

- [ ] Create a local Kenneth repair branch at exactly `1dc1b65`; do not push.
- [ ] Run build-check and confirm the source-faithfulness test fails while any global `Monotone alpha` premise remains.
- [ ] In the Kenneth file, change the four theorem/helper premises to `MonotoneOn alpha (Set.Icc a b)` and pass the interval premise directly into `SourceHypotheses`.
- [ ] Build in Kenneth layout, run forbidden/axiom checks, and commit only the Theorem 1.4 repair.
- [ ] Seed `draft.lean` from that committed Kenneth file, changing only the module import prefix.
- [ ] Run `python run_chapter.py --phase 2 --phase2-mode build-check --tasks thm_1_4` until the candidate builds.
- [ ] Run direct regression builds for `ToyApollo.Output.def_1_3` and `ToyApollo.Output.def_1_4` against the candidate-compatible dependency surface.
- [ ] Generate `review-now --review-subject candidate`, delegate independent read-only review, and write the bound result JSON.
- [ ] Run `review-apply`; if it does not project to `phase2_status=pass`, resume `auto-loop` rather than promoting manually.

### Task 3: Reconcile the Kenneth Theorem 1.1 proof family

**Files:**
- Modify first: `../_review-worktrees/kenneth-ProbabilityTheory-1dc1b65-thm1_2/ProbabilityTheory/chapter_01/thm_1_1*.lean`
- Modify candidate: `../toy-apollo-artifacts/campaigns/ch1-kenneth-1dc1b65-thm11-thm14-repair-20260712/phase2_prompt_packs/thm_1_1/draft.lean`
- Modify support candidates only as generated/declared by the Phase 2 pack.
- Promote on pass: `ToyApollo/Output/thm_1_1.lean` and mechanically necessary stable support files.

- [ ] Run direct build to reproduce the `Partition.noConfusion`/missing `DarbouxRS` interface failure.
- [ ] Reconcile the proof family with the prioritized Kenneth Definition 1.2 contract: eliminate the root `Partition` collision, provide the expected partition/core interface, and use the correct Fin tag/index types without changing the finite-discontinuity proof route.
- [ ] Replace theorem-level global `Monotone alpha` with `MonotoneOn alpha (Icc a b)` and propagate the local premise through source hypotheses and support lemmas.
- [ ] Build all Kenneth support modules, run forbidden/axiom checks, and commit the Theorem 1.1/API repair separately from Theorem 1.4.
- [ ] Seed the ToyApollo parent/support candidate from the committed Kenneth proof family, translating only module prefixes and declared support paths.
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
- [ ] Generate `git diff 1dc1b65..HEAD --stat`, per-file diffs, and `git format-patch` from the local Kenneth repair branch.
- [ ] Write a hash/commit mapping from Kenneth files to promoted ToyApollo files and their three-gate evidence.
- [ ] Commit only reviewed ToyApollo source/support changes and the design/plan; do not push either remote.
