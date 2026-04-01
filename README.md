# Toy Apollo

Toy Apollo 是一个 Lean 4 教材自动形式化流水线，保留四阶段执行模型：

- Phase 1: `inputs/*.tex` -> `plans/*_plan.json`
- Phase 2: 执行计划，生成 Lean 产物并本地验证
- Phase 3: 失败任务卸载到 Aristotle 云端
- Phase 4: 回收云端结果并对齐本地编译环境

## 快速开始（Windows PowerShell）

1. 安装 Lean / Lake（与 `lean-toolchain` 对齐）
2. 安装 Python 依赖：

```powershell
pip install -r requirements.txt
```

3. 配置密钥（当前默认策略：`src/config.py` 已内置硬编码 key；环境变量可选覆盖）：

```powershell
$env:GOOGLE_API_KEY="..."
$env:ARISTOTLE_API_KEY="..."
$env:MODEL_NAME="gemini-3-flash-preview"
$env:ARCHITECT_MODEL_NAME="gemini-3-pro-preview"
```

说明：
- 本轮结构收尾按既定策略保留硬编码 key，优先保证可运行。
- 若设置了同名环境变量，将覆盖 `src/config.py` 默认值。
- 安全加固（全面迁移到环境变量）将在后续独立计划中处理。

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
python .\run_chapter.py --phase 1 --input .\inputs
python .\run_chapter.py --phase 2 --input .\plans
python .\run_chapter.py --phase 3
python .\run_chapter.py --phase 4
python .\run_chapter.py --status
```

## 仓库边界

- 本仓库只保留源码、配置和最小输入。
- 运行产物（输出、日志、归档、大文件）应进入 `toy-apollo-artifacts` 仓库。
- 一键同步脚本：`.\tools\sync_artifacts.ps1 -Mode push|pull`
- 仓库卫生检查：`python .\tools\check_repo_hygiene.py`
