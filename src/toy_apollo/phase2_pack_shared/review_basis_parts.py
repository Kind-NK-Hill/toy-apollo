from __future__ import annotations

from typing import Any


def dedupe_strings(values: list[str]) -> list[str]:
    seen: set[str] = set()
    deduped: list[str] = []
    for value in values:
        normalized = str(value or "").strip()
        if not normalized or normalized in seen:
            continue
        seen.add(normalized)
        deduped.append(normalized)
    return deduped


def review_spine_contract(task: dict[str, Any]) -> dict[str, Any]:
    task_type = str(task.get("type", "") or "").strip().lower()
    requires_spine_review = task_type == "definition" or task_type.startswith("theorem") or "example" in task_type
    return {
        "required_for_pass": requires_spine_review,
        "general_rule": (
            "Pass requires the reviewer to identify the source proof/construction spine and point to its "
            "landing place in Lean; statement preserved plus downstream usable is not enough."
        ),
        "acceptable_abstraction": [
            "You may compress local proof detail or reuse Mathlib lemmas.",
            "You may not replace a source-side interface translation, proof-debt support item, construction chain, contradiction spine, partition argument, or other intermediate obligation with an opaque shortcut that leaves the source burden unaccounted for.",
        ],
        "automatic_fail_patterns": [
            "A source-side obligation is moved into a new theorem-level assumption.",
            "A source proof/construction spine is replaced by a theorem-specific wrapper or black-box substitution.",
            "The reviewer cannot say where the source-side obligations land in Lean but still proposes pass.",
        ],
        "pass_evidence_requirements": [
            "List the source-side obligations checked.",
            "Name the Lean landing place for each checked obligation.",
            "Explain why any abstraction used is faithful rather than a substitution.",
        ],
    }


def review_allowed_abstractions(task: dict[str, Any]) -> list[str]:
    task_type = str(task.get("type", "") or "").strip().lower()
    lines = [
        "可以在证明内部调用 Mathlib 或已有测度论/积分论引理，但导出的 theorem/definition statement 必须忠实对应教材对象。",
    ]
    if task_type.startswith("theorem"):
        lines.extend(
            [
                "可以引入局部 helper lemma，但不能把全局 theorem 偷换成更弱、局部或带额外结构假设的版本。",
                "可以在 proof spine 上做抽象化压缩，但不能跳过教材真正依赖的桥接对象或中间结论。",
            ]
        )
    elif task_type == "definition":
        lines.extend(
            [
                "可以新增 supporting structures/lemmas，但导出的定义不能退化成 existential shell 或 placeholder。",
                "若定义承担公共接口职责，review 必须按下游可消费性而不是单文件可编译性判断。",
            ]
        )
    elif "example" in task_type:
        lines.extend(
            [
                "可以用离散化、有限支撑或等价编码复现教材构造，但必须保留原结论、关键构造和反例/计算逻辑。",
            ]
        )
    return lines


def review_forbidden_weakenings(task: dict[str, Any]) -> list[str]:
    task_id = task["block_id"]
    task_type = str(task.get("type", "") or "").strip().lower()
    weakenings = [
        "禁止把教材中的公共接口偷换成纯存在性壳、占位定义或只记录 witness 的结构。",
        "禁止把应当供下游复用的 theorem 改写成只够当前文件自证的 theorem-specific wrapper。",
    ]
    if task_type.startswith("theorem"):
        weakenings.append("禁止通过额外 theorem-level 假设来掩盖上游接口缺口，除非任务文本本身明确包含该假设。")
    if task_id == "thm_1_4":
        weakenings.extend(
            [
                "禁止把教材中基于 partition 与 mean value theorem 的 Riemann--Stieltjes sum 主线整体压扁成 `withDensity` / `restrict` shortcut，然后仅以“proof spine compression”名义通过 review。",
                "禁止把 closed-interval (`Icc`) 结论偷换成只在 `Ioc` / density-restrict translation 上成立的局部版本。",
            ]
        )
    elif task_id == "thm_7_8":
        weakenings.extend(
            [
                "禁止把有限区间 LS↔RS interface translation 弱化成纯 measure-side interval integral 等式，却无法支撑 thm_7_9 的 improper RS 主线。",
                "禁止把端点无原子条件扩张为教材外的结构性假设。",
                "禁止让 direct downstream 在 `[-n,n]` 截断调用时额外补充新的端点原子假设；如果做不到无新增假设实例化，则 thm_7_8 不得通过。",
            ]
        )
    elif task_id == "thm_7_9":
        weakenings.extend(
            [
                "禁止绕开 def_1_4 的 improper RS 定义，直接用 measure-side shortcut 代替教材主线。",
                "禁止把 finite-interval interface translation 缩成局部可用版本，再在 thm_7_9 中偷偷补 theorem-level 新假设。",
            ]
        )
    elif task_id == "thm_7_12":
        weakenings.extend(
            [
                "禁止绕开 thm_7_9，直接从 LS 积分跳到 ordinary integral。",
                "禁止把 `LS -> improper RS -> ordinary integral` 压扁成一跳式 measure-side shortcut。",
            ]
        )
    elif task_id == "def_1_2":
        weakenings.append("禁止把 RS integrability 定义成 Nonempty witness 之类的抽象壳，而不暴露 partition / sum / integral 接口。")
    elif task_id == "def_1_4":
        weakenings.extend(
            [
                "禁止把 improper RS 定义成 `∃ I, True` 或任何不含双端截断极限内容的占位壳。",
                "禁止用 `else 0`、`default` 或任意 fallback 值掩盖 divergence / undefinedness。",
                "若定义拆成 convergence predicate + chosen value，禁止让 downstream 能在没有收敛证明的情况下直接消费 chosen value。",
            ]
        )
    elif task_id == "thm_8_6":
        weakenings.append("禁止只 formalize 离散分支却 promote 为总 theorem；若连续分支未覆盖，总 theorem 不得通过。")
    elif task_id == "ex_8_4_3":
        weakenings.append("禁止绕开 thm_8_6_discrete 自己手搓一套 Bernoulli-vs-Poisson TV 推导。")
    elif task_id == "thm_8_7":
        weakenings.append("禁止在 thm_8_7 内重新定义 totalVariationDistance；必须消费 def_8_5 的公共定义。")
    return dedupe_strings(weakenings)


def review_history_risks(task_id: str) -> list[str]:
    risks: dict[str, list[str]] = {
        "thm_1_4": [
            "历史风险是把教材的 partition + mean value theorem -> Stieltjes sum interface translation 换成 `restrict (Ioc a b)` / `withDensity` shortcut，若 reviewer 不追问转换义务，容易误判为等价压缩。",
            "历史风险是依赖 singleton-zero 与 `Icc -> Ioc` translation 补丁来收尾，使 closed-interval 结论看似成立，但教材主线里的转换对象已被抽空。",
        ],
        "def_1_2": [
            "历史版本把 RS integrability 退化成 `Nonempty` witness 壳，下游无法从中抽取可复用接口。",
        ],
        "def_1_4": [
            "历史版本把 improper RS integral 写成 `∃ I, True` 占位壳，无法支撑 thm_7_9 / thm_7_12。",
            "历史版本曾用 `else 0` 作为 divergence fallback，导致定义在语义上掩盖了“积分不存在”。",
        ],
        "thm_7_8": [
            "历史版本只给出有限区间上的局部 measure-side translation，review 通过后仍不足以支撑 thm_7_9。",
            "历史版本要求额外端点无原子条件，导致 thm_7_9 的 `[-n,n]` 截断主线无法无新增假设复用。",
        ],
        "thm_7_12": [
            "历史主线风险是直接走 measure-side shortcut，跳过 thm_7_9 所需的 improper RS 接口。",
        ],
        "thm_8_6": [
            "历史主线风险是只 formalize 离散 half，或把 continuous case 留成“similar proof”的空壳。",
        ],
        "thm_8_7": [
            "历史版本在 theorem 文件里复制定义 totalVariationDistance，削弱了 def_8_5 的公共接口地位。",
        ],
    }
    return list(risks.get(task_id, []))


def review_downstream_checklist(task_id: str) -> list[str]:
    checks: dict[str, list[str]] = {
        "thm_1_4": [
            "必须检查教材 proof spine 中的 partition / mean value theorem / Riemann--Stieltjes sum rewrite 是否被真实 discharge；若 reviewer 只能看到 density-side shortcut 而找不到这些桥接义务的落点，verdict 必须为 fail。",
            "必须检查 `Icc` textbook statement 不是靠 `Icc -> Ioc` + singleton-zero patching 偷换出来的局部 measure translation；若核心论证只在 `Ioc` restrict/density 层成立，verdict 必须为 fail。",
            "必须检查 thm_7_12 能直接消费 thm_1_4 而不新增假设；若 downstream 需要补 density translation、endpoint 处理或其他教材外 theorem-level 新增假设，verdict 必须为 fail。",
        ],
        "thm_7_8": [
            "必须检查 thm_7_9 能否在每个截断区间 `[-n,n]` 上直接实例化 thm_7_8，而不新增教材外 theorem-level 假设。",
            "若候选版本只在局部区间语义下成立，但 closed-interval textbook 消费路径需要额外补端点条件，则 verdict 必须为 fail。",
        ],
        "def_1_4": [
            "必须检查 downstream 是否只能在收敛已证明的前提下读取 improper RS 的具体值。",
            "若 exported definition 通过 fallback 数值掩盖 divergence，或把收敛失败编码成一个普通数值，verdict 必须为 fail。",
        ],
        "thm_7_9": [
            "必须检查证明主线是否真实经过修好的 thm_7_8 与 def_1_4，而不是直接改写成 measure-side shortcut。",
        ],
        "thm_7_12": [
            "必须检查证明是否真实经过 `LS -> improper RS -> ordinary integral`，并显式消费 thm_7_9。",
        ],
    }
    return list(checks.get(task_id, []))


def build_legacy_intent_contract(task: dict[str, Any]) -> dict[str, Any]:
    from .. import phase2_pack_generation as pack

    return pack.build_legacy_intent_contract(task)
