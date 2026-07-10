# Phase2 Review Harness Hardening Design

## 目标

让“全量复审”只通过一个受版本控制、可测试的正式决策边界得出结论。sidecar 可以隔离调度状态，但不得自行把 reviewer JSON 解释为 `pass`，也不得直接写入正式 ledger。

## 已确认的缺陷

1. 结果模板要求 reviewer 填写 `proof_class` / `completion_class`，但模板顶层和 schema hints 没有这两个字段，normalizer 也不要求字段存在。
2. ignored harness collector 绕过正式 `normalize_reviewer_result` 与 `classify_phase2_task_status`，因而可能把正式门会降级的结果记作 pass。
3. `review-apply` 在 task-status gate 前写 canonical review artifacts、proof obligations 和 ledger；格式或分类失败会改变下一次 freshness basis。
4. existing-output subject 按 mtime 选择，旧 shadow 可以盖过 canonical `ToyApollo/Output/<task>.lean`。
5. review basis 的 `source_evidence.tex_hash` 实际只 hash 了 plan task content，没有绑定 `inputs/<source_plan>.tex`。

## 设计

### 1. 单一只读决策入口

新增受版本控制的纯函数入口，把以下两步固定串联：

1. `normalize_reviewer_result(raw, review_input, runner_metadata)`；
2. `classify_phase2_task_status(...)`。

入口返回 normalized result、官方 task-status projection 和是否可作为 clean pass。任何 reviewer 自报的 `phase2_status` / `task_status` 都会被官方 projection 覆盖，不能成为 authority。`review-apply` 与 tracked collector CLI 共用该入口。

### 2. 显式 class 契约

`proof_class` 与 `completion_class` 成为 reviewer result 的必备键；模板顶层和 schema hints 同时出现。非 pass 可以使用空字符串，但 pass 缺失或为空不能成为 task-level pass。系统不猜测 proof class。

### 3. 先判定、后变更

`review-apply` 在写 canonical result、proof obligations、review history 或 ledger 前完成：identity、schema、hash、freshness、normalization 和 task-status projection。operational-invalid 结果直接返回，不污染 basis。有效 semantic fail 仍可进入 repair 记录；clean pass 才进入完成/提升路径。

### 4. Canonical subject binding

existing-output 的权威顺序固定为：

1. `ToyApollo/Output/<task>.lean`；
2. `output_lean_files/general/<task>.lean`；
3. `output_lean_files/<source_plan>/<task>.lean`。

mtime 只用于诊断，不再用于 subject selection。shadow divergence 继续报告，不能静默改变复审对象。

### 5. 真实 source TeX binding

`source_evidence` 同时记录 task-content hash 和 `inputs/<source_plan>.tex` 的路径、存在性与内容 hash。review generation 与 apply freshness 使用同一 basis，TeX 内容改变会使旧 review 失效。

## 数据流

`review request -> independent reviewer JSON -> official normalize -> official task projection -> freshness/preflight -> apply mutations`

sidecar 只保存调度状态和对正式结果的引用；最终 ledger 仍只能由 `review-apply` 更新。

## 非目标

- 不把现有 sidecar tally 直接迁入 ledger。
- 不在本改动中批量 apply Ch3 staged 结果。
- 不擅自登记 `ex_3_1_2` / `ex_3_1_4` 为 allowed exceptions。
- 不触碰主工作树中其他代理留下的 Lean、TeX 或 prompt-pack 改动。

## 验证标准

- 模板和 normalizer 对 class 字段保持一致；缺字段得到 operational inconclusive。
- reviewer 自报 pass 不能覆盖官方 projection。
- operational-invalid apply 前后 proof obligations、ledger 和 canonical review artifacts 不变，并可用修正后的同一 request 重试。
- canonical output 即使 mtime 更旧也被选择。
- 修改 source TeX（不改 plan task content）会触发 basis freshness failure。
- 现有 Phase2 review 测试与新增回归测试全部通过。
