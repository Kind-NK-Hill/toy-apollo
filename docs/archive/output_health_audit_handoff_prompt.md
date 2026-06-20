# ToyApollo Output Health Audit Handoff Prompt

把下面整段 prompt 交给新的 LLM。它的任务是先调查、质询文档、建立评价标准，并输出健康队列；第一轮不要直接改 Lean。

````text
你现在接手 ToyApollo 的 post-Phase2 output health audit / reorganization planning 任务。

你的第一目标不是改 Lean，而是调查、质询、建立判断标准，并输出一个健康队列。不要依赖前一个 LLM 的记忆或总结；所有判断必须来自本地文件、docs、Output、Support、phase2 artifacts、build/review 证据。

工作目录：
D:\Grad_Study\Practimum\Formalization\toy-apollo

请始终用中文汇报。

重要限制：
- 第一轮只读，不要修改 Lean 文件。
- 不要修改 ledger。
- 不要修改 phase2_status。
- 不要执行 review-apply。
- 不要手删历史记录。
- 不要预设哪些 task 一定健康或不健康；必须自己核验。
- 不要按字符串排序 review 版本；`v9` 不一定比 `v11` 新。优先读 canonical `semantic_review_result.json`，或按 LastWriteTime / 数字版本判断最新 artifact。

你需要使用 `grill-with-docs` 风格工作：
- 先读项目 docs、Output、Support、phase2 artifacts，再提问。
- 如果问题能通过代码或文档调查回答，就自己调查，不要问用户。
- 如果术语模糊，例如 “healthy”、“support”、“foundational”、“interface”、“bridge”、“OBL/OPL”，要指出歧义并提出推荐定义。
- 如果必须问用户，一次只问一个高价值问题，并给出你的推荐答案。
- 本轮不要直接更新 docs，除非用户明确允许；先输出“建议写入 docs 的定义/ADR”。

## 第一阶段：调查范围

请扫描这些位置：

- `ToyApollo/Output/*.lean`
- `ToyApollo/Support/*.lean`
- `phase2_prompt_packs/*/semantic_review_result.json`
- `phase2_prompt_packs/*/semantic_review_result_v*.json`
- `phase2_prompt_packs/*/metadata.json`
- `phase2_prompt_packs/*/proof_obligations.json`
- `docs/phase2/*.md`
- 其他你认为与 workflow/status/review 相关的本地文档

建议先收集：

```powershell
Get-ChildItem ToyApollo\Output -Filter *.lean |
  Sort-Object Length -Descending |
  Select-Object Name,Length -First 100
```

```powershell
Get-ChildItem ToyApollo\Support -Filter *.lean |
  Sort-Object Length -Descending |
  Select-Object Name,Length
```

```powershell
rg -n "\b(sorry|admit|axiom|unsafe)\b|^\s*import\s+ToyApollo\.Output\.obl_|^\s*(theorem|lemma|def)\s+obl_" ToyApollo\Output ToyApollo\Support
```

```powershell
rg -n "bridge|interface|support|foundational|allowed_exception|source_route|source_faithful|open_math_debt|statement" docs phase2_prompt_packs
```

## 第二阶段：核心输出

请输出一个健康审计表：

| Priority | File / Family | Size | Review Evidence | Build Evidence | Health Status | Main Issue | Recommended Action | Risk | Validation Needed |
|---|---:|---:|---|---|---|---|---|---|---|

Health Status 只能用这些类别或你明确定义的新类别：

- `healthy`
- `healthy-but-large`
- `needs-parent-split`
- `needs-support-split`
- `shared-support-candidate`
- `foundational-support-candidate`
- `interface-support-candidate`
- `duplicate-support`
- `legacy-noise`
- `source-statement-risk`
- `exception-boundary`
- `defer`

## 第三阶段：评价标准

criteria 是最重要部分。请按下面 rubric 判断，不要只按文件大小排序。

### 1. Parent 健康度

Parent file 指 task-facing theorem file，也就是用户和下游最容易 import 的文件。

Good:
- parent 很薄，只保留教材注释、必要 imports、final theorem。
- final theorem name/source-facing statement 不漂移。
- 没有把 proof machinery 堆在 parent 里。

Warning:
- parent 有少量 local helper。
- parent 10KB-30KB，但结构仍清楚。

Bad:
- parent 超过 50KB。
- parent 混合定义、模型、证明、bridge、review residue。
- final theorem 暴露非教材前提或 local proof-debt wrapper。

判断动作：
- Bad parent 通常先做 parent split。
- 不要先抽象大 theorem；先把 source-facing parent 稳住。

### 2. Support 健康度

Support file 可以大于 parent，但必须职责清楚。

Good:
- 文件围绕一个明确 proof layer。
- 名字和 import 方向稳定。
- 被 parent 或上层 support 单向 import。
- 没有隐藏 public theorem pollution。

Warning:
- support 40KB-80KB，但结构清楚。
- 有一些长 proof，但没有重复职责。

Bad:
- support 超过 100KB 且混合多个数学主题。
- 同一文件同时承担 model、measureability、limit theorem、final theorem bridge。
- 包含历史 obligation 名字、bridge debt、或重复别的 support。

判断动作：
- Bad support 通常先 split 成 parent-owned support layers。
- 只有发现第二个真实 consumer 时，才 promote 到 shared/foundational support。

### 3. Foundational Support 判据

Foundational support 是项目级或章节级的稳定数学基础，不属于某一道题。

Promote 的条件：
- 概念本身不是某个 task 专属。
- 至少两个 families 使用，或明显会被多个 later tasks 使用。
- theorem/definition 名字不带单一 task 前缀。
- import surface 小而稳定。
- 不包含 source-specific proof route。
- 不包含 proof-debt wrapper、temporary bridge、historical obligation name。
- 用成熟 Mathlib API 时，应该尽量包成稳定接口，而不是重造底层轮子。

不要 promote 的情况：
- 只有一个 consumer。
- 只是为了缩短一个文件。
- 带有具体 exercise/problem 的 pattern、constants、setup。
- 依赖某个 source theorem 的特殊 wording。
- abstraction 会导致 final theorem statement drift。

输出时必须给每个候选标注：
- `promote now`
- `parent-owned for now`
- `defer until second consumer`
- `do not promote`

### 4. Interface / TAO Interface Support 判据

Interface support 不是纯数学基础，而是把三层东西接起来：

1. textbook/source statement
2. ToyApollo local definitions and conventions
3. Mathlib mature API

适合 interface support 的内容：
- source terminology 到 local formalization 的稳定翻译。
- repeated theorem-interface wrappers。
- 多个任务都需要的 stopping-time / filtration / convergence / density / integration / distribution interface。
- Mathlib 已成熟，但 ToyApollo 需要固定教材口径的入口。

不适合 interface support 的内容：
- 单题具体计算。
- 单题 proof spine。
- 为了让某个 proof pass 临时加的 premise。
- historical obligation wrapper。
- 暴露 open math debt 的 public theorem。

判断问题：
- 这个 declaration 是在表达数学事实，还是在翻译接口？
- 如果 Mathlib 已有成熟 theorem，这里是不是只需要 thin adapter？
- adapter 是否有教材稳定意义，还是只是某个 proof 的 workaround？
- 这个 interface 是否会让 downstream theorem 更 source-facing，还是引入更多 public premise？

### 5. Duplicate / Overlap 判据

值得处理的 duplicate signal：

- 同一数学对象，不同 task prefix。
- 同一 theorem shape，只换了局部名字。
- 同一 proof skeleton 重复出现在多个 parent-owned support。
- 重复 unfold/simp bridge blocks。
- 重复 measurability/integrability/density/Jacobian/change-of-variable machinery。
- 重复 stopping-time/natural-filtration/interface wrappers。
- 重复 finite-product/probability kernel/convolution logic。

False duplicate：
- 看起来相似，但 source role 不同。
- 一个是 theorem proof，另一个是 interface statement。
- 一个是 concrete model，另一个是 general support。
- 两个文件 share shape，但 constants/overlap tables/source theorem statements 不同，抽象会造成 statement drift。

动作：
- exact duplicate -> delete or redirect, after import check。
- near duplicate with two consumers -> propose shared support。
- near duplicate but source-specific -> keep parent-owned, maybe split。
- abstraction high risk -> defer and document why。

### 6. Review / Status 判据

不要只看“build 过”。

Good:
- latest official output builds。
- latest semantic review is pass/high。
- canonical `semantic_review_result.json` agrees with latest numbered result。
- final theorem statement unchanged.
- no review-apply needed for this cleanup stage unless explicitly requested.

Warning:
- review pass exists but older than current Output。
- build-check refuses stale draft but existing-output review is fresh。
- phase2_status field missing in old artifact but verdict pass/high exists。

Bad:
- latest review fail/inconclusive。
- source statement decision required。
- review pass only applies to old candidate, not current Output。
- task is allowed exception but being treated as ordinary clean proof。

### 7. Forbidden / Debt Markers

Bad unless proven to be harmless comment-only context:

- `sorry`
- `admit`
- `axiom`
- `unsafe`
- import of `ToyApollo.Output.obl_*`
- top-level declarations named `obl_*`
- final theorem requiring public proof-debt premise
- theorem whose statement is not source-facing

But be precise:
- comment mentioning old obligation filename is not necessarily a blocker。
- hidden legacy ledger entries are not automatically files to delete。
- do not hand-edit ledger to “clean” status。

### 8. Deletion 判据

Delete only if all are true:
- file is actual unused temp/staging artifact, or compatibility shell with no remaining consumer;
- not tracked or explicitly approved;
- import/reference scan confirms no downstream use;
- deletion does not affect review artifact authority;
- user has allowed deletion if it is not obviously temporary.

Do not delete:
- proof evidence just because name looks ugly;
- support file with theorem-level evidence;
- ledger/status artifact;
- phase2 review artifact;
- anything needed to justify semantic pass.

### 9. Prioritization Rule

Rank candidates by expected health gain divided by risk.

High priority:
- passed task with huge parent file;
- passed family with duplicated support already used by more than one task;
- public `obl_*`/bridge-debt surface in official Output;
- parent imports sibling concrete support in wrong direction;
- support file over 100KB with mixed concerns.

Medium priority:
- passed large support but parent already thin;
- clear split candidate but no duplicate;
- readability cleanup after fresh review.

Low priority:
- already split and reviewed;
- only linter style warnings;
- one-off concrete proof whose abstraction would be risky;
- failed/source-decision task not suitable for shrinking.

Do not prioritize:
- tasks whose source statement is unresolved;
- allowed exceptions unless checking boundary hygiene;
- hidden legacy obligations;
- remark/intro noise.

## 第四阶段：Grill With Docs

在输出最终队列前，请进行一次“docs grilling”：

1. 找出 docs 中已有的 workflow/status/support 定义。
2. 对照代码实际情况，指出术语冲突。
3. 对这些术语给出推荐定义：
   - `healthy`
   - `parent`
   - `parent-owned support`
   - `shared support`
   - `foundational support`
   - `interface support`
   - `bridge`
   - `legacy obligation`
   - `allowed exception`
   - `source-facing theorem`
4. 如果 docs 与实际 workflow 不一致，列出建议更新，但不要直接改。
5. 如果必须问用户，只问一个最关键问题，并附你的推荐答案。

## 第五阶段：最终报告格式

请输出：

### 1. Investigation Summary

- 读了哪些 docs。
- 扫了哪些 directories。
- 使用了哪些 commands。
- 哪些 evidence 是最新的。
- 哪些 evidence 可能 stale。

### 2. Criteria

用你最终采用的 criteria 重新定义 health，而不是只复制 prompt。

### 3. Health Queue

输出 top 10 或 top 15 files/families。

### 4. First Target Recommendation

只选一个 first target。

格式：

```text
Current main target: ...
Reason: ...
Not choosing ... because ...
Completion signal:
- build ...
- no forbidden debt scan ...
- fresh existing-output semantic review ...
- docs/criteria note updated or proposed ...
```

### 5. Do-Not-Touch List

列出当前不应动的文件/任务类型，并说明原因。

### 6. Questions For User

最多问 1-3 个问题。每个问题必须有推荐答案。

不要在第一轮 implementation。
不要改 Lean。
不要改 ledger。
不要 review-apply。
````
