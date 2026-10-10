# Lin-program

本目录是独立研究尝试，保存上游程序、资料、参考形式化及探索项目；部分制品仍被当前证书重放使用。
本项目的固定输入、解释、局部证书和可移植重放入口位于
[`KIP126/LinProgram/`](../KIP126/LinProgram/README.md)。
主工程采用的证书模块已复制到 KIP126 自行维护；主库不从本目录导入 Lean 模块，独立尝试的源码继续保留。
实际球面认证由 `KIP126/Interface/Solution/LinProgram/` 负责。
各项后续工作的位置见[任务归属表](../KIP126/LinProgram/README.md#任务归属与继续开发入口)。

## 文档资料

步骤一的论文程序边界、Kervaire 论文依赖位置、输入输出和计算性结论保存在
[`doc_data/`](doc_data/)：

- [`step1_inventory.md`](doc_data/step1_inventory.md)：详细分析报告；
- [`program_boundary.md`](doc_data/program_boundary.md)：程序边界说明；
- [`kervaire_dependency_locations.md`](doc_data/kervaire_dependency_locations.md)：Kervaire 论文依赖位置说明；
- [`kervaire_program_inventory.json`](doc_data/kervaire_program_inventory.json)：结构化清单；
- [`kervaire_claims.csv`](doc_data/kervaire_claims.csv)：待形式化的关键结论；
- [`sources.md`](doc_data/sources.md)：论文、源码和数据集来源。

## 形式化准备

Lin Program 所涉及数学概念的细粒度依赖路线图保存在
[`Reference/`](Reference/)：

- [`roadmap.html`](Reference/roadmap.html)：可缩放、可拖动、可搜索的完整概念依赖图；
- [`roadmap.svg`](Reference/roadmap.svg)：可直接在编辑器中打开的矢量图；
- [`roadmap_view.md`](Reference/roadmap_view.md)：在 VS Code / code-server 中使用 Markdown 预览查看图；
- [`roadmap.md`](Reference/roadmap.md)：每个节点的数学定义、Lean 表示、依赖和可靠性接口；
- [`render_dependency_graph.py`](Reference/render_dependency_graph.py)：从 `roadmap.md` 重新生成网页和 SVG。

`Reference/LinProgramReference/` 是步骤三的 Lean 形式化入口，根文件为
[`LinProgramReference.lean`](Reference/LinProgramReference.lean)，项目配置和构建说明见
[`Reference/README.md`](Reference/README.md)。
形式化语义审查见 [`Reference/SEMANTIC_AUDIT.md`](Reference/SEMANTIC_AUDIT.md)。
数学概念覆盖审计见
[`Reference/MATHEMATICAL_COVERAGE_AUDIT.md`](Reference/MATHEMATICAL_COVERAGE_AUDIT.md)。

## 克隆与数据恢复

克隆时使用 `git clone --recurse-submodules`；已有克隆运行
`git submodule update --init --recursive`，以恢复固定版本的 SSeqCpp 源码。
Lean 依赖、构建缓存和本地编译产物不纳入版本控制，按各子项目说明重新构建。

三份原始证明 CSV 超过 GitHub 普通 Git 的单文件大小限制，因此以
[`program/upstream/proofs_csv.rar`](program/upstream/proofs_csv.rar) 保存。
提交前已逐份核对压缩包内数据与本地 CSV 的 SHA-256 完全一致。
在仓库根目录运行以下命令恢复：

```sh
unrar x -o- program/upstream/proofs_csv.rar program/upstream/
```

若未安装 `unrar`，可先运行 `make -C program/upstream/unrar`，然后将上述命令中的
`unrar` 替换为 `program/upstream/unrar/unrar`。
