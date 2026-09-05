# 安装与操作指南

公开仓库可用于构建 Lean 正文、开发运行时、查看历史案例，以及运行一个完整的隔离演示。
教材原文、完整任务计划、私有目录策略和运行数据库不随公开版本发布。
项目介绍和个人贡献见[中文首页](../README.zh-CN.md)。

## 公开仓库快速开始

需要 Python 3.11 及以上、Git、与 `lean-toolchain` 对齐的 Lean/Elan。
完整测试还需要 `rg`。持续集成使用 Ubuntu 和 Python 3.12；以下采用 Windows PowerShell。

```powershell
git clone https://github.com/Kind-NK-Hill/ProbabilityTheoryFormalization.git
Set-Location .\ProbabilityTheoryFormalization
python -m venv .venv
.\.venv\Scripts\Activate.ps1
python -m pip install --editable .
lake exe cache get
formalize -h
formalize --status
python tools/run_workflow_demo.py
```

优先使用仓库固定的 Lean 工具链和依赖清单。依赖尚未初始化或需要有意更新时再用 `lake update`。
Python 依赖尚未完全锁定，不能把声明的最低版本理解成完整兼容性保证。

[完整演示](workflow_demo.md)调用正式的任务准备、构建、审查请求、结果校验和接受函数，
使用真实 Lean 编译和独立 SQLite 数据库，演示缺失条件、调用方修复和旧审查失效。
默认回放已登记的教学审查，不调用新模型；外部审查适配器的配置见演示文档。
生成目录会保留供检查，不能将其结果导入教材目录或当成新的独立审查。

只有需要语义索引或检索时，才安装额外组件：
`python -m pip install -e ".[retrieval]"`，也可使用 `requirements.txt`。
核心材料包和完整演示不需要这些检索依赖。

## 验证代码与公开版本

在未修改的公开版本中执行：

```powershell
python tools/check_public_release.py
python tools/check_formal_corpus.py --publication-map data/publication/corpus_map.json
python tools/check_case_studies.py
lake build ProbabilityTheory
python tools/check_chapter_imports.py
python -m unittest discover -s tests -p "test_*.py" -v
```

发布校验核对文件范围和按 UTF-8/LF 规范化的内容摘要，修改文件后出现不匹配是预期行为。
全库构建检查所有正文模块及依赖；章节联合导入另行检查，第一、七章仍保留教材与 Mathlib
的 `Partition` 边界。编译通过不等于已证明符合教材原意。

查看一个模块可以运行 `lake build ProbabilityTheory.chapter_08.def_8_5`。
历史案例的前后切片均可单独编译，语义差异见[案例目录](../examples/case-studies/README.md)。
更完整的检查说明见[开发指南](development.md)。

## 完整本地工作区

下面的教材处理操作需要自备来源材料、任务计划、目录策略和证据库。
公开 `manifest_by_chapter.csv` 只有文件名、路径、模块、章节和摘要，不含审查状态，
不能替代完整任务目录。因此 `formalize state validate` 不属于公开克隆的快速检查。

完整工作区可通过环境变量指定根目录：

```powershell
$env:FORMALIZATION_ENGINE_RUNTIME_ROOT = "C:\work\ProbabilityTheoryFormalization"
$env:FORMALIZATION_ENGINE_ARTIFACT_ROOT = "C:\work\ProbabilityTheoryFormalization-artifacts"
formalize --status
formalize state validate --json
```

`--status` 只读，报告当前进程解析到的位置。目录验证、与当前代码完全匹配的审查覆盖、
类型化证据和其他候选的维护需求是不同维度。`worklist` 的行数不代表尚未完成的教材任务数。
`status <task>` 和 `worklist` 默认刷新仓库与 GitHub 观察，但不会自动提交、推送、创建或合并拉取请求。

## 教材处理流程

| 阶段 | 工作 |
| --- | --- |
| 0：来源整理 | 将 PDF 页范围整理为干净的 TeX 单元 |
| 1：任务规划 | 生成材料包，由作者编写任务草案，再校验并应用 |
| 2：形式化 | 准备候选、编译、独立审查、根据问题修复、接受当前有效结果 |

第二阶段的推荐命令顺序：

```powershell
formalize --phase 2 --phase2-mode pack --tasks ex_4_4_3
formalize --phase 2 --phase2-mode build-check --tasks ex_4_4_3
formalize --phase 2 --phase2-mode review-now --tasks ex_4_4_3 --review-subject candidate
formalize --phase 2 --phase2-mode review-apply --tasks ex_4_4_3 --review-result <审查结果文件路径>
```

材料包中的 `draft.lean` 由作者或编写智能体编辑；`review-now` 准备请求，由外层任务派发
独立审查者。仅准备请求不是完成。审查失败或无法判定时，先记录结果，再通过 `auto-loop`
继续诊断和修复。具体状态、预算和停止条件见[工作流](phase2/workflow.md)及
[审查契约](phase2/agent_review_contract.md)。

习题的软依赖选择使用 `soft-pack` 与 `soft-apply`；它们不调用外部证明服务，也不是编译验收。
`--tasks` 仅用于第二阶段相关模式。第一阶段应用命令的 `--input` 指向原始 TeX 或输入目录，
不是任务草案文件。完整命令通过 `formalize -h` 查询。

## 状态与写入范围

`ProbabilityTheory/` 是唯一正式 Lean 正文。普通编写、构建和审查准备写入制品目录；
只有针对当前对象的 `review-apply` 可以更新清单解析出的正式文件，失败时恢复原内容。
外部 Kenneth/MAT 仓库是审查来源。`pr-review prepare/apply` 只登记准确 PR 版本的审查，
不自动写入正文或改变 PR 合并状态。

运行制品、旧账本、来源材料和历史记录即使未被 Git 跟踪也应保留。
更多说明见[状态管理](workspace_state.md)、[发布范围](repository_scope.md)和[安全策略](../SECURITY.md)。
