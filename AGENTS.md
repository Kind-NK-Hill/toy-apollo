# AGENTS 协作说明（Toy Apollo）

## 1) 项目目标（当前代码语义）
- 本项目是一个 **Lean 4 自动形式化流水线**：把 `inputs/*.tex` 的教材内容拆解为任务，自动生成 Lean 代码，编译验证，并将结果落盘到章节目录与 `ToyApollo/Output`。
- 主控脚本是 `run_chapter.py`，按 Phase 1-4 驱动。
- 当前仓库历史显示此前由 Gemini 驱动；你已明确弃用 Gemini，但**代码层仍大量绑定 Gemini 与 Aristotle**（见第 6 节）。

## 2) 当前状态快照（本地盘点于 2026-03-30）
- `inputs`: 12 个 `.tex`
- `plans`: 12 个 `*_plan.json` + `unsolved_tasks.json`
- `formalized_chapters`: 11 个章节汇总 `.lean`
- `output_lean_files`: 185 个 `.lean`
- `ToyApollo/Output`: 38 个 `.lean`
- `project_ledger.json`: `tasks_total=119`  
  `COMPLETED=33`, `DISCOVERED=82`, `FAILED_LOCAL=4`
- `lake build`（默认目标 `ToyApollo`）当前失败：`ToyApollo.lean` 有 unresolved goals/unknown identifiers  
  但单模块（例如 `lake build ToyApollo.Output.def_3_1`）可通过。

## 3) 目录职责（高频）
- `src/`: Python 核心实现（编排、检索、编译、账本、云端卸载）
- `inputs/`: LaTeX 输入
- `plans/`: 任务分块 JSON（parser 输出）
- `output_lean_files/<chapter>/`: 每任务产物
- `output_lean_files/general/`: 通用/补救产物（含 phase3/phase4 回流结果）
- `ToyApollo/Output/`: Lean 编译镜像目录（模块化导入目标）
- `formalized_chapters/`: 每章合并文档
- `error_logs/<chapter>/`: 各任务日志
- `reports/*_report.md`: 章节运行报告
- `project_ledger.json`: 全局任务状态机与输出哈希
- `research_notes/`: 研究文档（非运行时）

## 4) 运行入口与命令
- 查看帮助：
  - `python run_chapter.py -h`
- Phase 1（LaTeX -> 计划）：
  - `python run_chapter.py --phase 1 --input inputs`
  - 或单文件：`python run_chapter.py --phase 1 --input inputs/01_chap3_premeasure.tex`
- Phase 2（本地自动形式化）：
  - `python run_chapter.py --phase 2 --input plans`
  - 或单计划：`python run_chapter.py --phase 2 --input plans/01_chap3_premeasure_plan.json`
- Phase 3（Aristotle 卸载失败任务）：
  - `python run_chapter.py --phase 3`
- Phase 4（对齐云端结果并回编译）：
  - `python run_chapter.py --phase 4`
- 状态总览：
  - `python run_chapter.py --status`

## 5) 核心代码地图（必须先读）
- `run_chapter.py`
  - 顶层 phase 调度，串接 parser/orchestrator/offloader/ledger
- `src/orchestrator.py`
  - 任务队列主循环、缓存命中、依赖注入、分解策略、失败回退与日志
- `src/pipeline.py`
  - 生成-编译-反馈循环（guided + rescue）、REPL 校验、retrofit、对齐
- `src/compiler.py`
  - Lean REPL 校验 + `lake build` 定向编译（`ToyApollo.Output.Temp_Validation`）
- `src/context_manager.py`
  - 依赖传递闭包、成功代码池、失败签名池
- `src/searcher.py` + `src/indexer.py`
  - 本地 Mathlib 向量检索（FAISS + sentence-transformers）+ rerank
- `src/ledger_manager.py`
  - 任务生命周期状态机、哈希审计、符号索引
- `src/aristotle_offloader.py` + `src/aristotle_phase3.py` + `src/aristotle_bridge.py`
  - 云端打包/提交/收割/本地回流

## 6) 关键技术债与迁移事实（与“弃用 Gemini”直接相关）
- `src/config.py` 仍硬编码：
  - `GOOGLE_API_KEY`
  - `MODEL_NAME="gemini-3-flash-preview"`
  - `ARCHITECT_MODEL_NAME="gemini-3-pro-preview"`
  - `ARISTOTLE_API_KEY`
- 多模块直接依赖 `google.genai` 客户端（`agent.py`, `textbook_parser.py`, `architect.py`, `parser.py`, `searcher.py`）。
- 结论：若正式弃用 Gemini，需要先完成“模型后端抽象/替换”再谈功能迭代；否则 pipeline 默认仍会走 Gemini。

## 7) 数据契约（实现时常用）
- `plans/*.json` 每个 task 基本字段：
  - `block_id`, `type`, `title`, `content`, `dependencies`
  - 常见附加：`is_renowned`, `source_plan`, `depth`
- Ledger 状态枚举（`TaskStatus`）：
  - `DISCOVERED -> LOCAL_FIXING -> FAILED_LOCAL -> OFFLOADED -> HARVESTED -> ALIGNING -> COMPLETED`
  - 旁路状态：`USER_MODIFIED`, `ORPHANED`

## 8) 当前协作约束（给后续 Codex/人工）
- 先以模块为单位验证：`lake build ToyApollo.Output.<block_id>`，不要把 `ToyApollo.lean` 当作唯一健康指标。
- 不要删除 `project_ledger.json`；它是重试与增量执行基线。
- `output_lean_files` 与 `ToyApollo/Output` 是双产物区，修改时注意保持同步语义。
- 仓库当前是重度 dirty 状态（大量 `D`/`??`），执行 Git 操作前先明确“保留/清理”策略。

## 9) 建议的下一步（按优先级）
1. 先把密钥迁移到环境变量，移除 `src/config.py` 中明文密钥。  
2. 抽象 `LLMProvider`，把 Gemini 调用封装到单层适配器，便于替换为新后端。  
3. 将 `ToyApollo.lean` 与流水线产物解耦（或修复默认 target），避免 `lake build` 总体误报失败。  
4. 补齐最小 `README`/`requirements.txt`，固定 Python 依赖版本，降低环境漂移。  
