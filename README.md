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

3. 配置环境变量（不要把密钥写入代码）：

```powershell
$env:GOOGLE_API_KEY="..."
$env:ARISTOTLE_API_KEY="..."
$env:MODEL_NAME="gemini-3-flash-preview"
$env:ARCHITECT_MODEL_NAME="gemini-3-pro-preview"
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
