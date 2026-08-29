# Toy Apollo

Toy Apollo 是一个 Lean 4 教材自动形式化流水线，当前执行模型是：

- Phase 0: source PDF/page range -> cleaned `inputs/*.tex`
- Phase 1: `pack` -> agent/human writes `draft_plan.json` -> `apply` writes `plans/*_plan.json`
- Phase 2: 本地 formalization 与验证
- Phase 2 Problem 特例: soft dependency selection（`soft-pack` / `soft-apply`）

注：

- `--status` 严格只读；它只显示本进程解析到的 roots 和 ledger 摘要，不声明活动 campaign 的全局 authority。
- Protected 不等于 tracked；ignored 不等于 deletion candidate。
- 项目完成度只由固定 catalog 对现有 `state.sqlite3` 的 `state validate` 结果判定。
- `worklist` 显示工作树候选的 review/rebind/promotion 维护动作；即使其中有很多行，也不等于相同数量的 catalog 必需任务未完成。

## 快速开始（Windows PowerShell）

1. 安装 Lean / Lake（与 `lean-toolchain` 对齐）
2. 安装 Python 依赖：

```powershell
pip install -r requirements.txt
```

3. 查看当前 secret 要求：

- Phase 0/1/2 prompt-pack 和 Problem soft dependency workflow 不需要旧的 DeepSeek/Gemini direct-generation key。
- Phase 2 Problem soft dependency workflow 不需要外部 provider key。
- 不要把密钥写入代码或提交到 Git 历史。
- 建议使用系统环境变量，不要在项目根目录放置 `.env` 文件。

可选路径覆盖（不改 CLI，用于从其他工作目录启动当前 workspace）：

```powershell
$env:TOY_APOLLO_RUNTIME_ROOT="D:\Grad_Study\Practimum\Formalization\toy-apollo"
$env:TOY_APOLLO_ARTIFACT_ROOT="D:\Grad_Study\Practimum\Formalization\toy-apollo-artifacts"
```

4. 查看命令帮助：

```powershell
python .\run_chapter.py -h
```

## 常用命令

```powershell
python .\run_chapter.py --phase 0 --phase0-mode pack --input <source.pdf> --page-range <start-end> --phase0-output <output_stem>
python .\run_chapter.py --phase 0 --phase0-mode validate --phase0-output <output_stem>
python .\run_chapter.py --phase 0 --phase0-mode apply --phase0-output <output_stem>
python .\run_chapter.py --phase 1 --phase1-mode pack --input .\inputs\<source>.tex
python .\run_chapter.py --phase 1 --phase1-mode apply --input .\inputs\<source>.tex
python .\run_chapter.py --phase 1 --phase1-mode apply --input .\inputs
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks ex_1_2_3
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks thm_4_7
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks thm_4_7 --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks thm_4_7 --review-result .\phase2_prompt_packs\thm_4_7\semantic_review_result_vN.json
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_4_2,prob_4_4
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks prob_4_2,prob_4_4 --selection .\selection.json
python .\run_chapter.py --status
python .\run_chapter.py status thm_1_1
python .\run_chapter.py worklist  # candidate maintenance, not catalog completion
python .\run_chapter.py state validate --json
python .\run_chapter.py pr-review prepare --task ex_1_3_1 --pr 9 --checkout <clean-exact-head-checkout>
```

`--status` 会显示 artifact、plan、ledger、Phase 1/2 prompt-pack、dependency-decision 和 Output roots，同时报告 `TOY_APOLLO_RUNTIME_ROOT` / `TOY_APOLLO_ARTIFACT_ROOT` 是否设置。`STATUS_SCOPE=resolved_for_this_process_not_global_authority` 表示这些值只对当前进程成立。

`status <task>` 与 `worklist` 查询工作区级 `toy-apollo-artifacts/state.sqlite3`，并默认刷新本地 Git 与 Kenneth GitHub 状态；它们不会自动 commit、push、开 PR 或 merge。完整规则见 `docs/workspace_state.md`。旧 `project_ledger.json` 在数据库启用后只作为冻结的兼容/迁移证据。

Kenneth PR 的语义复审使用 `pr-review prepare/apply`：它把审查绑定到准确的 PR head、文件包和构建收据，且绝不把外部候选写入 `ToyApollo/Output`。该命令也不会修改 PR 的 draft/ready/merge 状态。

`--tasks` 适用范围：

- `--tasks` 用于 Phase 2 prompt-pack/review modes 和 Problem soft dependency modes。
- Phase 0/1 不支持 `--tasks`；Phase 1 apply 的 `--input` 应指向原始 source `.tex` 或 `inputs` 目录，而不是 `draft_plan.json`。

Problem soft dependency 任务过滤示例：

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_3_1,prob_3_2
```

Problem task 的 soft imports 必须先通过 `soft-pack -> soft-apply` 写入 `soft_imports_confirmed_at`，空列表也需要显式确认。

## 推荐的 Phase 2 路径

推荐的本地 formalization 路径现在是：

1. `pack`
2. 在 `phase2_prompt_packs/<task_id>/draft.lean` 中由 Codex 编辑
3. `build-check`
4. `review-now --review-subject candidate`
5. 独立、只读 reviewer 写入 fresh semantic review result
6. `review-apply`
7. 若 review fail/inconclusive，先由 `review-apply` 记录 repair evidence，再进入 `auto-loop`

CLI completion [active phase=2]: `pack -> build-check -> review-now -> review-apply`.

示例：

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks ex_4_4_3
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks ex_4_4_3
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks ex_4_4_3 --review-subject candidate
python .\run_chapter.py --phase 2 --phase2-mode review-apply --tasks ex_4_4_3 --review-result .\phase2_prompt_packs\ex_4_4_3\semantic_review_result_vN.json
```

说明：

- `pack -> build-check -> review-now -> review-apply` 是推荐主路径；`review-now` 本身不是完成点
- 旧 direct-generation/orchestrator Phase 2 路径已从 active CLI 移除
- 新路径强制依赖本地 Mathlib grounding 与本地验证
- 对带证明或解答的任务，必须回到 `inputs/<source>.tex` 检查原始证明主线；prompt pack 中的复制文本只是镜像。
- `hard_failure` 是最后手段，必须有原始 TeX proof-spine 拆解和具体 blocker 记录，不能用来代替大证明的分解工作。
- 复杂证明任务必须先写 task-local decomposition/reconstruction plan；拆新 obligation 前要先查 `ToyApollo/Output`、ledger、dependency decisions、plans 和 Mathlib，已有输出要复用或修元数据；under-evidenced hard stop 后重试时，完成前或累计 15 次 substantive build/review failure 前不能再次 hard-failure。

权威 runbook 见：

- `docs/phase2/workflow.md`

## 仓库边界

- 本仓库只保留源码、配置和最小输入。
- `ToyApollo.lean` 是库级 smoke test；教材章节输出位于 `ToyApollo/Output/`，不要把两者混为一谈。
- 正式化文件只允许从 ToyApollo 单向进入 `MAT3280-formalization-output` 精炼库；MAT 的审查结果不得回写 `ToyApollo/Output/`。
- Kenneth 文件需要复审时，必须复制到 MAT 的 review 分支处理；通过后再由 PR 返回 Kenneth，不得先放进 ToyApollo。
- `Kind-NK-Hill/ProbabilityTheory` 只承载发给 Kenneth 的 PR 分支，不是第四份正式内容库。
- 运行产物（输出、日志、归档、大文件）应进入 `toy-apollo-artifacts` 仓库。
- 被保护的运行状态不一定要进入 Git；被 ignore 的文件也不是删除候选。
- 一键同步脚本：`.\tools\sync_artifacts.ps1 -Mode push|pull`
- 仓库卫生检查：`python .\tools\check_repo_hygiene.py`
- 统一 workspace/SQLite/452-task 状态：`python .\tools\workspace_status.py --write --compare-latest-rebuild`
- agent 入口：`AGENTS.md`
- 按需规则：`.claude/rules/`
