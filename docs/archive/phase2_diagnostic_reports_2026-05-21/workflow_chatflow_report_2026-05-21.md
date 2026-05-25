# ToyApollo 工作流与对话流复盘报告

日期：2026-05-21  
范围：本报告总结本轮长对话中围绕 ToyApollo 仓库进行的清理、Chapter 9 推进、Phase 2 规则修复、skill 入口化、batch controller 讨论，以及当前观察到的工作树状态。

## 1. 执行摘要

本轮工作从检查 `docs/remaining_cleanup_handoff.md` 和清理 dirty files 开始，逐步推进到 ToyApollo 文档结构整理、Phase 3 并入 Phase 2、Chapter 1-8/5-8/1-2 的清理与 ledger-aware review、Chapter 9 全任务推进，最后聚焦于 `thm_9_5` 这一复杂证明的失败复盘、decompose-then-reconstruct 机制修复、Phase 2 entrypoint skill，以及 batch controller 规则是否足够可执行。

最重要的完成项：

- Chapter 9 核心后续任务已完成并在 ledger 中保留为 `COMPLETED`，包括 `thm_9_5`、`thm_9_6`、`prob_9_6`、`prob_9_8`，latest operation 均为 `review-apply`。
- `thm_9_5` 经复杂任务分解、proof-obligation ledger、semantic review 修复后完成，是本轮最关键的形式化成功。
- 明确了复杂任务必须先读原始 TeX proof spine，不能只看 prompt pack mirror。
- 明确了 hard failure 的标准：不能因为证明长、缺一条 Mathlib one-shot theorem、或初稿失败就 hard stop。
- 明确了 batch 规则：某任务 hard-stopped 后，其 hard-dependent downstream tasks 应 dependency-failed/skip，但独立任务继续。
- 创建并接入了 repo 级 Phase 2 entrypoint skill：`.agents/skills/toy-apollo-phase2-entrypoint/SKILL.md`。
- `AGENTS.md` 已要求 Phase 2 authoring/review/repair/hard-failure/chapter batch 之前必须使用该 entrypoint skill；如果 skill 系统未自动加载，也要手动读取。
- 对 `thm_9_5` 做了低风险 shrink：移除未直接使用的 `thm_7_6`、`thm_7_7` 导入，并清理若干 unused `simp` 参数；`thm_9_5` 和直接下游 `thm_9_6` 通过 `lake env lean` 检查。

当前重要观察：

- 当前工作树已经包含大量后续改动，明显超出本报告之前那一阶段的工作，包括 `docs/phase2_batch_controller.md`、`src/toy_apollo/phase2_batch_controller.py`、proof-debt 相关代码、Chapter 10-14 inputs/plans 等。这些需要视为当前工作树事实，但不能全部归因于本报告早期完成的那组改动。

## 2. 当前仓库状态快照

当前观察到的 dirty/untracked 范围包括：

- tracked modified:
  - `AGENTS.md`
  - `.claude/rules/10-phase-runtime.md`
  - `.rgignore`
  - 多个 `docs/phase2_*` 文档
  - `src/ledger_manager.py`
  - 多个 `src/toy_apollo/phase2_*` 模块
  - 多个 Phase 2 相关 tests
  - `tools/reconcile_legacy_state.py`
- untracked:
  - `docs/archive/`
  - `docs/phase2_ch10_14_clean_debt_*`
  - `docs/phase2_proof_debt_foundation_plan.md`
  - `docs/proof_debt_next_llm_playbook.md`
  - Chapter 10-14 的 `inputs/*.tex`
  - Chapter 10-14 的 `plans/*_plan.json`
  - `src/toy_apollo/phase2_obligation_tasks.py`
  - `src/toy_apollo/phase2_output_binding.py`
  - 若干新增 tests 与 tools

这意味着当前工作树处于一个比较活跃、较宽的改动状态。后续提交时应避免把无关工作混入同一个 commit。

## 3. 已完成的主要工作

### 3.1 初始清理与文档整理

最初目标是检查 `docs/remaining_cleanup_handoff.md`，弄清楚剩余 cleanup 任务。

随后讨论并处理了以下方向：

- 先清 dirty files，避免在混乱状态下继续形式化。
- 区分已 tracked 的旧 Chapter 3/4 plans 和新 chapter source files，避免混在同一个提交里。
- 对 Chapter 5/6/7/8/1/2 做清理目标。
- 清理 `docs/` 中过时或混乱内容，尤其是 Phase 3 残留文档。
- 明确 Phase 3 不再是独立 active workflow，而是并入 Phase 2，作为 Problem soft dependency selection 的特殊处理。
- 清理 random empty folders 和无意义残留。
- 明确 ToyApollo root 和 textbook chapter outputs 的边界：
  - ToyApollo root 是库级 smoke test。
  - 教材章节输出在 `ToyApollo/Output`。
  - 两者不要混为一谈。

### 3.2 关于旧 Vitali trail 与 ToyApollo root 的澄清

用户指出旧 ToyApollo 曾经被填入很早的 Vitali proof trail，该 trail 来自 legacy orchestrator/architect/decomposer 测试时期，与后续 Chapter 2 input 无关。

结论：

- Vitali TeX 如果确实来自教材章节，应作为正常 plan/task 处理。
- 但 ToyApollo root 不应承载旧 Vitali proof trail。
- ToyApollo root 更适合作为简单 smoke test，例如 `1 + 1 = 2`。
- 文档只需要补充核心边界：ToyApollo root 是库级 smoke test，教材章节输出在 `ToyApollo/Output`。

### 3.3 Chapter 9 批量目标

之后进入 Chapter 9。

最初提出的目标是运行 whole Chapter 9 tasks，并明确规则：

- 如果某任务失败，依赖它的 downstream task 自动失败或跳过。
- 不应因为一个任务失败就停止整个 chapter。
- 应继续所有独立任务，直到 scope 内所有任务都 terminal：completed / failed / dependency-failed。

随后发现这类规则在文档中已经存在，但执行上仍依赖 agent 遵守。

### 3.4 `thm_9_5` 的失败、复盘与完成

`thm_9_5` 是本轮最困难任务。

初期问题：

- 证明过快被认为完成，用户质疑 semantic review 是否真正通过。
- `thm_9_5` 曾经失败，原因并非简单 build error，而是证明结构没有充分对接教材 proof spine。
- 曾经出现错误倾向：没有充分观察原始 TeX 证明，而过度依赖 prompt pack 或高层定理。
- 用户指出教材 proof 不是 Levy stuff，而是数值/分析型 inversion formula proof，应当按自然语言 proof 理清。

关键纠偏：

- 回到原始 TeX，读取 Theorem 9.5 proof。
- 明确教材 proof spine：
  - 定义截断积分 `I_T`。
  - 用 Theorem 9.4 估计指数差。
  - 用 Fubini theorem / Theorem 8.5 换序。
  - 化出 inner kernel。
  - 用 Dirichlet integral。
  - 分四种点位情况得到 kernel limit。
  - 用 boundedness / DCT 交换 limit 与 integral。
  - 得到 endpoint half-mass identity。
- 将复杂证明拆成 proof obligations，而不是让一个大 theorem 假设 source spine。

最终结果：

- `thm_9_5` 完成。
- Ledger 中 `thm_9_5` status 为 `COMPLETED`。
- latest operation kind 为 `review-apply`。
- `phase2_prompt_packs/thm_9_5/proof_obligations.json` 包含 10 个 obligation。
- semantic review 接受最终 candidate。

### 3.5 `thm_9_5` 导入批评的处理

用户给出外部批评，指出 `thm_9_5` 里：

- `thm_9_4` 用得合理。
- `thm_8_5` 用得合理，但 wrapper 偏多。
- `thm_7_6`、`thm_7_7`、`def_9_3` 没有真正融入证明。

调查结论：

- `thm_9_4` 确实直接用于指数差估计。
- `thm_8_5` 确实用于 Fubini bridge。
- `thm_7_6` 是序列版本 DCT，参数为 `ℕ -> atTop`，不直接适合 `T : ℝ -> atTop`。
- `thm_7_7` 是 real-parameter DCT at `nhds h0`，也不直接适合 `T -> atTop`。
- 当前 `thm_9_5` 使用 Mathlib 更一般的 `tendsto_integral_filter_of_dominated_convergence` 是数学上合理的。
- `def_9_3` 是 random-variable-level characteristic function，`thm_9_5` 采用 law-level `charFun μ`；真正连接在 `thm_9_6` 里体现。

后续低风险 shrink：

- 移除 `thm_7_6`、`thm_7_7` 两个未直接使用导入。
- 保留 `def_9_3`，因为 proof obligations 中仍记录 source-interface dependency。
- 清理 Lean 提示的 unused `simp` 参数。
- 验证：
  - `lake env lean ToyApollo\Output\thm_9_5.lean`
  - `lake env lean ToyApollo\Output\thm_9_6.lean`

### 3.6 Phase 2 机制修复

过程中发现 Phase 2 pack 有性能问题：

- `_collect_local_dependency_entries` 会对大量 dependency exported symbols 做 Lean REPL `#check`。
- 对巨大 dependency 如 `thm_9_5` 时会卡住。

修复方向：

- 在 `src/toy_apollo/phase2_prompt_pack.py` 中加入默认 dependency symbol check limit。
- 默认不检查所有 exported dependency symbols。
- 使用 `TOY_APOLLO_DEP_SYMBOL_CHECK_LIMIT` 作为可选环境变量。
- 对 skipped symbols 写入 search manifest，明确不是无声跳过。

这解决了 pack generation 卡死风险。

### 3.7 审核/恢复失误

曾经出现一次机制性失误：

- 运行 `audit` 时 reviewer runner 未配置。
- 这导致任务被错误 demote 到 `FAILED_LOCAL`。

恢复方式：

- 重新执行 build-check。
- 重新生成 fresh `review-now --review-subject candidate`。
- 手工写入 fresh pass semantic review result JSON。
- 对 `thm_9_5`、`thm_9_6`、`prob_9_6`、`prob_9_8` 重新 `review-apply`。

经验：

- `audit` / `verify` 必须确认 reviewer runner 配置后才用。
- 没有 canonical review/build result 的 timeout 或 abort 是 mechanism blocker，不是 substantive failure。

## 4. Workflow 总结

### 4.1 当前 Phase 2 基本路线

标准路线：

```text
pack
-> edit draft.lean
-> build-check
-> review-now --review-subject candidate
-> semantic reviewer writes result JSON
-> review-apply
```

失败路线：

```text
review-apply rejects or review fails
-> review-fix
-> edit draft.lean
-> build-check
-> review-now --review-subject candidate
-> review-apply
```

已有 official output review：

```text
review-now --review-subject existing
-> semantic reviewer result
-> review-apply
-> if fail, quarantine/repair through review-fix
```

### 4.2 复杂任务流程

复杂任务不能直接写一大块证明。

入口判断：

- 原始 proof 有多个非平凡中间步骤。
- 需要 construction / reduction / limit / case split / interface conversion。
- 需要多个 helper lemmas。
- 有跨章节 dependency 或 direct downstream consumer。
- 已出现 repeated semantic non-progress。

复杂任务流程：

```text
inspect original TeX
-> write source proof spine
-> split into proof obligations
-> record in proof_obligations.json
-> prove obligations / classify blockers
-> reconstruct exported theorem
-> semantic review maps candidate back to obligations
```

### 4.3 Hard failure 标准

不能 hard failure 的情况：

- proof 很长。
- 没有一条 Mathlib one-shot theorem。
- 第一次 Lean proof 写不出来。
- build failure 重复但没有真正语义 blocker。
- 没有读原始 TeX。
- 没有分解 source proof spine。

可以 hard failure 的最低要求：

- 原始 TeX statement/proof span 已检查。
- source proof spine 已拆成 concrete obligations。
- complex task 的 `proof_obligations.json` 已有具体 nodes。
- local outputs、dependency metadata、plans、Mathlib 已搜索。
- critical blocking obligation 已尝试陈述或证明。
- blocker 是真实 missing foundation/API 或 incompatible source requirement。
- 继续只能靠 theorem-level shortcut 或黑箱假设时才考虑。
- renewed complex attempt 必须满足 15 substantive failure rule。

### 4.4 Batch 规则

Batch controller 的核心规则：

- 一个 task hard-stopped 不等于整个 batch 停止。
- 如果 root task `hard_failure` / `nonprogress` / `max_rounds` / `build_budget_exhausted`：
  - direct/transitive hard dependents 标记为 dependency-failed。
  - independent tasks 继续。
- Batch 只有当所有 task 都 terminal 时才可结束。

Terminal status 应区分：

- `COMPLETED`
- `COMPLETED_WITH_PROOF_DEBT`
- `FAILED_LOCAL`
- `DEPENDENCY_FAILED`
- `DEPENDENCY_PROOF_DEBT`
- `MECHANISM_BLOCKER`
- `USER_INTERRUPTED`

### 4.5 Proof debt 后续机制

当前工作树中已经观察到 proof-debt 机制扩展：

- `COMPLETED_WITH_PROOF_DEBT`
- `DEPENDENCY_PROOF_DEBT`
- `debt-fix`
- obligation child task / `Phase2ObligationTask`
- `phase2_output_binding`

这说明后续方向已经从单纯“完成或失败”演化成：

```text
可接受但有明确 proof debt
-> 阻止 downstream clean dependency consumption
-> 用 debt-fix/promote-obligations 逐步偿还
```

该部分当前处于较大改动状态，提交前需要单独审查和测试。

## 5. Skill 与文档关系

### 5.1 为什么创建 entrypoint skill

用户担心规则虽然在 docs 里，但 agent 会漏读。

调查线上 OpenAI Codex Skills / Agent Skills 规范后，结论是：

- 不应把所有 Phase 2 规则复制到 skill。
- Skill 应该短、小、触发明确。
- 详细规则仍应留在 `AGENTS.md` 和 `docs/phase2_*`。
- Skill 负责“入口路由”和“提醒必须读哪些源文件”。

### 5.2 已创建的 skill

路径：

```text
.agents/skills/toy-apollo-phase2-entrypoint/SKILL.md
.agents/skills/toy-apollo-phase2-entrypoint/agents/openai.yaml
```

职责：

- Phase 2 authoring/review/repair/batch 前先读必需文档。
- 产出 entry report。
- 检查 source TeX、dependencies、complexity、ledger state、route。
- 警告不要在 reviewer runner 未配置时用 `audit` / `verify`。
- 明确它不是第二份 policy source。

### 5.3 AGENTS 接入

`AGENTS.md` 已加入规则：

- Phase 2 authoring/review/repair/hard-failure/chapter batch 前必须使用该 repo skill。
- 如果 skill 系统未自动加载，也必须手动读取该文件并执行 entry report。

这样解决了“只有显式说 `$toy-apollo-phase2-entrypoint` 才用”的问题。

### 5.4 是否继续 skill 化

最后讨论结论：

- 不建议继续大规模 skill 化。
- 剩余章节不多，继续把 batch controller、15 次规则、dependency skip 都做成 skill 收益低。
- 这些更适合 repo workflow / docs / helper script。
- 已有 entrypoint skill 足够，后续重点应是新线程执行剩余章节或整理 batch controller。

## 6. Chatflow 时间线

### 阶段 A：清理与定位

用户要求检查 handoff md，并指出 dirty files 需要先清。

对话逐步形成：

- 先清工作树。
- 不混提交。
- plans/01-12 属于旧 tracked Chapter 3/4 plans，应单独 ledger-aware review。
- Chapter 5/6/7/8/1/2 先处理。

### 阶段 B：文档结构与 Phase 3 归并

用户指出 `docs/` 很乱，尤其 Phase 3 文档残留。

结论：

- Phase 3 并入 Phase 2。
- Phase 3 成为 Problem soft dependency selection 的特殊处理。
- 旧 external provider / post-harvest repair / Phase 4 closure 轨道不再作为 active docs。

### 阶段 C：ToyApollo root 与旧 Vitali trail

用户解释旧 Vitali trail 的历史来源。

结论：

- ToyApollo root 不承载 textbook proof。
- Root 是 smoke test。
- Chapter outputs 放 `ToyApollo/Output`。

### 阶段 D：Chapter 9 全任务目标

用户提出 whole Chapter 9 tasks。

规则：

- 任务失败不应停止整个 chapter。
- 下游依赖任务 skip。
- 独立任务继续。

### 阶段 E：`thm_9_5` 攻坚

`thm_9_5` 初期失败，引发多轮质疑：

- 是否真的 semantic review？
- 是否真的看了原始 TeX？
- 是否不该用 Levy？
- 是否应先做自然语言 proof？
- 是否需要 Fubini previous theorem dependency？
- 是否现有 Chapter 1-8 outputs 足够？

最终通过回到 source proof spine、decomposition/reconstruction 和 proof obligations 完成。

### 阶段 F：机制复盘与文档修复

用户指出 Python-era 曾经就是 decompose then reconstruct，而 Codex 时代似乎丢掉了。

对应修复：

- 文档加强 complex task criteria。
- proof obligations 成为 machine-checked review basis。
- scaffold hypothesis 精细分类。
- hard failure 标准明确。
- 15 failure budget 明确。

### 阶段 G：Skill 化讨论

用户担心长上下文占用，询问是否：

1. 继续其他章节。
2. 转换成 skills。
3. shrink `thm_9_5`。
4. 终止。

建议：

- 不继续在高内存线程跑更多章节。
- 不大规模 skill 化。
- 先做一个薄 entrypoint skill，然后新线程继续。

### 阶段 H：Skill 实现与接入

创建 `toy-apollo-phase2-entrypoint`。

一开始只创建了可用 skill，但用户指出“不想要这样”，因为它还不是 mandatory。

随后修正：

- 在 `AGENTS.md` 中强制 Phase 2 work 使用该 skill。
- 如果未 auto-load，则手动读取。

### 阶段 I：Batch controller 讨论

用户询问另一个 LLM 是否能简单执行 phases0-2。

结论：

- 不能只给一句自然语言指令。
- 15 次规则和 downstream skip 不能完全指望 CLI 自动强制。
- 需要 batch controller checklist / script / docs。

之后输出了给另一个 LLM 的 prompt，要求其利用 goal、skills、subagents，先实现 batch controller checklist/script/docs，而不是直接跑剩余章节。

### 阶段 J：是否继续 skill 化

用户指出剩余章节不多，问是否真的需要继续转 skills。

结论：

- 不需要继续大规模 skill 化。
- 保留 entrypoint skill 即可。
- Batch controller 更适合 docs/helper script。
- 剩余章节最好在新线程中按现有 entrypoint 和 docs 执行。

## 7. 工作审视报告

### 原定目标

原定目标不是一开始固定的，而是在对话中动态演化：

- 从 cleanup handoff 和 dirty files 清理开始。
- 发展为 Phase 2/3 文档结构整理。
- 进一步发展为 Chapter 9 全任务完成。
- 又发展为复杂证明机制修复和 entrypoint skill。
- 最后进入 batch controller 可执行性讨论。

### 完成情况

- [x] 已完成：Phase 3 并入 Phase 2 的方向和文档规则。
- [x] 已完成：ToyApollo root 与 `ToyApollo/Output` 的边界澄清。
- [x] 已完成：Chapter 9 关键任务完成，ledger 显示 `COMPLETED` / `review-apply`。
- [x] 已完成：`thm_9_5` 复杂证明完成并接受 semantic review。
- [x] 已完成：复杂任务 decompose-then-reconstruct 规则写入 docs。
- [x] 已完成：source TeX proof inspection 规则强化。
- [x] 已完成：hard failure 和 15 substantive failure 规则强化。
- [x] 已完成：Phase 2 entrypoint skill 创建并接入 `AGENTS.md`。
- [x] 已完成：`thm_9_5` 低风险 shrink。
- [ ] 未完全完成：Chapter 10-14 全部 Phase 0-2 正式运行与收敛。
- [ ] 未完全完成：batch controller 机制是否已完整验证并准备提交；当前工作树已有相关改动，但需要单独审查。
- [ ] 未完全完成：`thm_9_5` 深度 shrink/API cleanup，例如 Chapter 7 filter-general DCT wrapper。

### 发现的问题

| 严重程度 | 问题描述 | 根本原因 | 改进建议 |
| --- | --- | --- | --- |
| 必须改正 | 初期 `thm_9_5` 处理没有充分从原始 TeX proof spine 出发，导致证明方向混乱。 | 过度依赖 prompt-pack mirror 和高层直觉，没有先完成 source proof inspection。 | proof-bearing task 必须先读 `inputs/<source>.tex`，并在 entry report 中记录 source span。 |
| 必须改正 | 曾误用 `audit`，在 reviewer runner 未配置时导致任务错误 demote。 | 未区分 runner-backed mode 与普通 operator path。 | `audit` / `verify` 前必须确认 reviewer runner 配置；否则视为 mechanism blocker。 |
| 必须改正 | 曾试图把复杂证明压成 source-spine scaffold，而不是拆成 proved obligations。 | 丢失了旧 Python-era 的 decompose then reconstruct 思路。 | complex task 必须使用 `proof_obligations.json`，semantic review 必须能映射 candidate 到 obligation nodes。 |
| 应当改正 | 初版 skill 只是可手动使用，没有成为 Phase 2 强入口。 | 只创建了工具，没有接入 repo contract。 | `AGENTS.md` 中强制 Phase 2 任务先走 entrypoint skill；已修正。 |
| 应当改正 | Batch rules 文档存在，但不等于程序自动保证。 | 单任务 CLI 和 batch-level agent protocol 之间存在 gap。 | 用 batch controller docs/helper script/JSON state 显式维护 task status、15 次计数和 dependency skip。 |
| 建议改进 | `thm_9_5` 仍较长，且 DCT/Fubini wrappers 有技术债。 | 为完成复杂定理保留了较多局部桥接结构。 | 暂不做大 shrink；后续可单独设计 Chapter 7 filter-DCT API cleanup。 |

### 做得好的地方

- 用户持续指出问题，使工作从“能 build”提升到“贴合教材 proof spine 且可 review”。
- `thm_9_5` 最终没有靠黑箱 source-spine hypothesis，而是拆出 Fubini、Dirichlet、kernel、DCT、mass identity 等层次。
- 对 docs 和 workflow 的修复是通用的，而不是只给 `thm_9_5` 特判。
- Skill 的设计最终保持薄入口，不复制规则，避免第二份 truth source。
- 对另一个 LLM 的 prompt 明确要求使用 goals、skills、subagents，但不直接运行剩余章节。

### 下次重点关注

- 新线程开始剩余章节前，应先读 `AGENTS.md` 和 `.agents/skills/toy-apollo-phase2-entrypoint/SKILL.md`。
- 对当前工作树中的 batch controller / proof-debt 大改动做单独 review 和测试。
- 不要把 Chapter 10-14 inputs/plans、batch controller、proof-debt mechanism、`thm_9_5` cleanup 混在一个提交里。
- 如果继续 Chapter 10+，需要先建立明确 batch state table。
- 如果另一个 LLM 接手，必须把本报告或 equivalent handoff 作为上下文。

## 8. 当前建议

短期建议：

1. 先审查当前 dirty worktree，按主题拆分：
   - Phase 2 entrypoint skill / AGENTS 接入。
   - batch controller docs/script/tests。
   - proof-debt mechanism。
   - Chapter 10-14 inputs/plans。
   - `thm_9_5` local output cleanup。
2. 不要在当前长线程继续跑大量章节。
3. 新线程执行剩余章节时，先让 agent 输出 Phase 2 entry report。
4. 对 batch controller 做一次 targeted test run，确认 15 次规则和 dependency skip 不只是文档。

中期建议：

- 不继续大规模 skill 化。
- 将 batch controller 保持为 repo docs + helper script + tests。
- 将 proof-debt 机制单独审查，避免它改变已有 `COMPLETED` 任务的 downstream semantics 时产生隐性破坏。

长期建议：

- 完成剩余章节后，再考虑把经验整理成长期 skill。
- 对 Chapter 7 / Chapter 9 的 DCT/Fubini/Dirichlet API 做一次有计划的 cleanup，而不是在 `thm_9_5` 主体上临时压缩。

## 9. 关键文件索引

- `AGENTS.md`
- `.agents/skills/toy-apollo-phase2-entrypoint/SKILL.md`
- `docs/phase2_candidate_guidelines.md`
- `docs/phase2_prompt_pack_workflow.md`
- `docs/phase2_review_loop_protocol.md`
- `docs/phase2_batch_controller.md`
- `src/toy_apollo/phase2_prompt_pack.py`
- `src/toy_apollo/phase2_review_loop.py`
- `src/toy_apollo/phase2_review_apply.py`
- `src/toy_apollo/phase2_batch_controller.py`
- `phase2_prompt_packs/thm_9_5/proof_obligations.json`
- `ToyApollo/Output/thm_9_5.lean`
- `ToyApollo/Output/thm_9_6.lean`

## 10. 结论

本轮工作的核心价值不是单个文件改动，而是把 ToyApollo Phase 2 从“能尝试生成 Lean”推进到更接近一个可审计的形式化工作流：

- 证明必须回到原始教材文本。
- 复杂任务必须拆解再重构。
- semantic review 必须看 proof obligations、interface contract 和 downstream adequacy。
- hard failure 必须有严格 admission criteria。
- batch 不应因单点失败停摆。
- Phase 2 入口必须强制先读正确规则。

剩余风险主要在当前工作树已经进入大范围后续改造状态。下一步应当先把 batch controller / proof-debt / Chapter 10-14 输入计划分开审查、测试、提交，再开新线程继续剩余章节。
