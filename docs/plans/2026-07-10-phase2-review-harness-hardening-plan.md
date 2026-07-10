# Phase2 Review Harness Hardening Implementation Plan

**Goal:** 把全量复审的 accept/reject 决策收敛到受版本控制的正式 normalizer + task projection，并修复 apply 原子性、canonical subject 与 source TeX freshness。

**Architecture:** 在 `src/toy_apollo` 提供纯只读 review decision API；`review-apply` 和 tracked collector 复用它。review request 继续携带完整 evidence，但 subject/source freshness 由 canonical path 与真实文件 hash 约束。

**Tech Stack:** Python 3、pytest、现有 ToyApollo Phase2 runtime。

---

### Task 1: Class schema 与统一 decision API

**Files:**
- Create: `src/toy_apollo/phase2_review_decision.py`
- Create: `tests/test_phase2_review_decision.py`
- Modify: `src/toy_apollo/phase2_semantic_review.py`
- Modify: `src/toy_apollo/phase2_prompt_pack.py`
- Modify: `tests/test_phase2_pack_generation.py`

1. 写失败测试：模板含 class 字段/hints，normalizer 缺键降级，raw task-status 不能覆盖 projection。
2. 运行相应测试确认 RED。
3. 实现最小 decision API 和 class schema/template 契约。
4. 运行相应测试确认 GREEN。

### Task 2: Canonical existing-output 与真实 source TeX binding

**Files:**
- Modify: `src/toy_apollo/phase2_pack_shared/artifacts.py`
- Modify: `src/toy_apollo/phase2_review_request.py`
- Modify: `src/toy_apollo/phase2_prompt_pack.py`
- Modify: `src/toy_apollo/phase2_review_loop.py`
- Modify: `tests/test_phase2_review_request.py`
- Modify: `tests/test_phase2_pack_generation.py`

1. 写失败测试：canonical output 比较旧仍被选中；仅修改 source TeX 会改变 basis/freshness。
2. 运行测试确认 RED。
3. 移除 mtime subject selection，记录真实 TeX path/existence/hash 与 task-content hash。
4. 统一 review-basis hash 调用点，运行测试确认 GREEN。

### Task 3: review-apply preflight 与无污染重试

**Files:**
- Modify: `src/toy_apollo/phase2_review_apply.py`
- Modify: `tests/test_phase2_review_apply.py`

1. 写失败测试：缺 class/operational-invalid apply 不改 proof obligations、ledger、canonical result/history；修正 result 后同一 request 可重试。
2. 运行测试确认 RED。
3. 把 normalize、freshness、decision projection 移到 mutation boundary 前；invalid 直接返回只读 outcome。
4. 保留有效 semantic fail 的 repair 行为与 clean pass landing 行为。
5. 运行 apply 测试确认 GREEN。

### Task 4: Tracked collector 边界

**Files:**
- Create: `tools/phase2_review_decision.py`
- Create/Modify: `tests/test_phase2_review_decision.py`

1. 写 CLI 测试：读取 review input/result，输出官方 normalized verdict、projection、clean-pass 布尔值；identity/schema mismatch 非零退出。
2. 实现仅调用 `src` decision API 的薄 CLI，不复制 validator 规则。
3. 运行测试确认 GREEN。

### Task 5: 回归与交接

1. 运行 targeted review suites。
2. 运行全量 Python tests（若仓库既有环境缺失，明确区分环境问题与代码回归）。
3. 审计 `git diff --check`、worktree 状态和主工作树未被改动。
4. 只读评估 Ch3 staged 结果；不 apply，输出 freshness/结构/policy 分类和下一批顺序。
