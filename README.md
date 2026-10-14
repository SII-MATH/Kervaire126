# Kervaire126

仓库：[SII-MATH/Kervaire126](https://github.com/SII-MATH/Kervaire126)。

用 Lean 形式化 *On the Last Kervaire Invariant Problem* 的标准 `h₆²` 非零永久存活结论。
项目仍在开发中；编译成功、导入计算数据和来源核对均不表示数学证明已经完成。

仓库名为 Kervaire126，Lean 包、库和命名空间继续使用 `KIP126`。
固定 Lean `4.32.2`、Mathlib `v4.32.2`；准确版本见 `lean-toolchain` 和 `lake-manifest.json`。

## 内容

- `KIP126/Def/`：数学对象、固定模型、通用定义和定理。
- `KIP126/Interface/`：关联的文献与计算交付，构造唯一 `Challenge2` 见证。
- `KIP126/Main/`：论文推导及最终目标。
- `KIP126/LinProgram/`：固定计算输入、翻译、生成数据、解释和局部证书。
- `KIP126/Checks/`：Lean 回归与边界检查。
- `blueprint/src/`：当前数学计划、声明链接、依赖与证明状态。
- `MainPaper/`：目标论文；`Source/`：外部来源及获取记录。
- `docs/external-inputs.json`：唯一来源与输入清单。

来源清单保留外部输入、带来源的适配器、模型绑定和交付义务；普通内部辅助
证明不逐条重复登记，其数学声明、依赖和状态由 Lean 源码及 Blueprint 记录。
小组件的数据没有独立消费者时，可在一个具名模块中按数据、性质、证明的顺序
组织；需要独立使用这些层时再拆分文件。整理须保留公开声明、证明及来源标注。

范围、信任与最终验收由 [PROJECT_BOUNDARY.md](PROJECT_BOUNDARY.md) 规定。
接口与证明责任见 [docs/STAGE0_INTERFACES.md](docs/STAGE0_INTERFACES.md)，
输入浏览视图见 [docs/challenge-input-inventory.html](docs/challenge-input-inventory.html)。
开发约束见 [AGENTS.md](AGENTS.md)。

SSData 与 Mathlib 谱序列之间的可选适配层由旧仓库
[SII-MATH/KIP126](https://github.com/SII-MATH/KIP126/tree/main/KIP126/Mathlib)
维护。本仓库保留内部 SSData 构造与主证明，继续使用上游 Mathlib 基础库。

## 构建与检查

安装 Elan、Git LFS 与 Python 3.10 或以上，从仓库根目录运行：

```sh
git lfs install --local
git lfs pull
lake exe cache get
lake build KIP126
bash scripts/check.sh
```

默认 `lake build` 和 CI 构建 KIP126。除下面明确恢复的 KIPBase 外，
`develop` 继续遵循 `main` 的剥离范围。
KIPBase 已按用户决定恢复为独立可选库，可显式运行 `lake build KIPBase`。
它不进入 KIP126 的导入图、默认构建或 CI；其历史公理不属于 KIP126 的证明输入。
旧审计与迁移档案、历史备份、Euler/Multica 配置及旧工作流和工具继续留在旧仓库，
后续同步不重新引入。已有代码的来源标注继续保留。

原始数据库、CSV 和 `Source/LWXMachine/kervaire_database.rar` 使用 Git LFS。
普通 Git 文件中的指针不能代替原始输入；
生成 Lean 数据保留在仓库中，重新翻译原始输入需要实际 LFS 文件。
当前重放使用的提取与重建记录位于 `KIP126/LinProgram/Generated/Provenance/`；
[LinProgram 说明](KIP126/LinProgram/README.md) 列出局部证书与实际比较的职责。

Blueprint 需要 Graphviz、LaTeX、Ghostscript、pdf2svg 和 `requirements-blueprint.txt` 中的固定 Python 依赖：

```sh
python3 -m venv .venv
.venv/bin/pip install -r requirements-blueprint.txt
PATH="$PWD/.venv/bin:$PATH" bash scripts/check-blueprint-decls.sh
```

API 文档可手动生成，不是默认 CI 门槛：

```sh
cd docbuild
lake build KIP126:docs
```

严格的最终证明验收工具保留为 `lake exe axioms`，不作为开发 CI 的通过条件。
现有未完成证明及临时 `Main.Axiom.challenge2` 保持原有状态。

本仓库的保留与删减清单见 [docs/REPOSITORY.md](docs/REPOSITORY.md)，
精简后的 CI 见 [docs/CI.md](docs/CI.md)。
