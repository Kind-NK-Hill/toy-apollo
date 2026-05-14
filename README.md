# Toy Apollo

Toy Apollo 是一个 Lean 4 教材自动形式化流水线，当前执行模型是：

- Phase 0: source PDF/page range -> cleaned `inputs/*.tex`
- Phase 1: `pack` -> agent/human writes `draft_plan.json` -> `apply` writes `plans/*_plan.json`
- Phase 2: 本地 formalization 与验证
- Phase 2 Problem 特例: soft dependency selection（`soft-pack` / `soft-apply`）
- Phase 3: merged into Phase 2；旧命令只给迁移提示
- Phase 4: disabled/no-op；旧自动回收/对齐流程仅作 legacy/manual 参考

注：

- 当前 CLI 中，Phase 4 自动分支 disabled/no-op。
- Protected 不等于 tracked；ignored 不等于 deletion candidate。

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

可选路径覆盖（不改 CLI，用于 artifacts 分仓）：

```powershell
$env:TOY_APOLLO_RUNTIME_ROOT="D:\Grad_Study\Practimum\toy_apollo_archive\_migration_20260330_211429\toy-apollo"
$env:TOY_APOLLO_ARTIFACT_ROOT="D:\Grad_Study\Practimum\toy_apollo_archive\_migration_20260330_211429\toy-apollo-artifacts"
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
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_4_2,prob_4_4
python .\run_chapter.py --phase 2 --phase2-mode soft-apply --tasks prob_4_2,prob_4_4 --selection .\selection.json
python .\run_chapter.py --status
```

`--tasks` 适用范围：

- `--tasks` 用于 Phase 2 prompt-pack/review modes 和 Problem soft dependency modes。
- Phase 0/1 不支持 `--tasks`；Phase 1 apply 的 `--input` 应指向原始 source `.tex` 或 `inputs` 目录，而不是 `draft_plan.json`。

Problem soft dependency 任务过滤示例：

```powershell
python .\run_chapter.py --phase 2 --phase2-mode soft-pack --tasks prob_3_1,prob_3_2
```

Problem task 的 soft imports 必须先通过 `soft-pack -> soft-apply` 写入 `soft_imports_confirmed_at`，空列表也需要显式确认。

当前状态：

- Phase 4 CLI 分支暂时禁用/no-op。
- 如需恢复自动对齐流程，应先修改代码与 runbook，再把命令重新写回 README。

## 推荐的 Phase 2 路径

推荐的本地 formalization 路径现在是：

1. `pack`
2. 在 `phase2_prompt_packs/<task_id>/draft.lean` 中由 Codex 编辑
3. `build-check`
4. `review-now --review-subject candidate`
5. 根据 build/review 结果继续下一轮

示例：

```powershell
python .\run_chapter.py --phase 2 --phase2-mode pack --tasks ex_4_4_3
python .\run_chapter.py --phase 2 --phase2-mode build-check --tasks ex_4_4_3
python .\run_chapter.py --phase 2 --phase2-mode review-now --tasks ex_4_4_3 --review-subject candidate
```

说明：

- `pack -> build-check -> review-now` 是推荐主路径
- 旧 direct-generation/orchestrator Phase 2 路径已从 active CLI 移除
- 新路径强制依赖本地 Mathlib grounding 与本地验证
- 对带证明或解答的任务，必须回到 `inputs/<source>.tex` 检查原始证明主线；prompt pack 中的复制文本只是镜像。
- `hard_failure` 是最后手段，必须有原始 TeX proof-spine 拆解和具体 blocker 记录，不能用来代替大证明的分解工作。

权威 runbook 见：

- `docs/phase2_prompt_pack_workflow.md`

## Phase 3/4 边界

Phase 3 已并入 Phase 2，作为 Problem soft dependency selection 的特殊处理：`--phase 2 --phase2-mode soft-pack/soft-apply`。旧 provider offload、post-harvest repair、Phase 4 closure 脚本和 runbook 不再作为 tracked operator docs 保留；如需恢复，必须先恢复对应 CLI 代码，再补回文档。

## 仓库边界

- 本仓库只保留源码、配置和最小输入。
- `ToyApollo.lean` 是库级 smoke test；教材章节输出位于 `ToyApollo/Output/`，不要把两者混为一谈。
- 运行产物（输出、日志、归档、大文件）应进入 `toy-apollo-artifacts` 仓库。
- 被保护的运行状态不一定要进入 Git；被 ignore 的文件也不是删除候选。
- 一键同步脚本：`.\tools\sync_artifacts.ps1 -Mode push|pull`
- 仓库卫生检查：`python .\tools\check_repo_hygiene.py`
- agent 入口：`AGENTS.md`
- 按需规则：`.claude/rules/`
