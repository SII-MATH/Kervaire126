# 仓库起点与核对清单

Kervaire126 从旧仓库 `SII-MATH/KIP126` 的 main 提取，起点提交：
`9d2601af4529ebcdd353ccc01fe09e0a463ed25a`（PR #157 的合并结果）。
旧仓库与 Git 历史保留；新仓库采用独立初始提交。Lean 包及公共命名空间保持 `KIP126`。
远程仓库为 [SII-MATH/Kervaire126](https://github.com/SII-MATH/Kervaire126)，当前为公开仓库。
Blueprint 尚未配置远程网站/API 链接。

以下迁入清单和本地核对结果记录新仓初始快照；`develop` 后续整合见下一节，
初始文件数量与核对结果不代表合并后的当前状态。

## develop 本地进展整合（2026-10-10）

- 合并旧仓本地开发历史与 Kervaire126 更新，保留本地 KIP126 证明进展。
- `develop` 与 `main` 使用同一剥离范围。清除合并重新带回的旧审计档案、
  归档工作流、Euler/Multica 配置及旧 CI、审查、合并、状态、缓存、性能和发布工具；
  不在当前源码树中保留这些设施的历史副本或专用测试。
- `KIPBase/`、`KIPBase.lean`、专用脚本与进展清单、`docs/migration/kip-base/`，
  以及 `KIPBase` 和 `kipbaseAudit` 构建目标继续保持剥离。
- 移除依赖未迁入的 `Prover-all` 和本地工作流的工具入口与配置。
- 保留 KIP126 数学源码、Blueprint 更新、原始来源制品与已有来源标注。
  旧提交仍存在于 Git 历史中；当前文件树遵循下面的迁入边界。
- 同步最新 `main` 的精简 CI 与编译缓存优化，保留 `develop` 推送触发。
  当前验证入口为来源、接口、Blueprint 检查及完整 KIP126 构建。

## LinProgram 进展整合

当前整合以 Kervaire126 的 `develop` 为基础，保留其 Lean `module` / `public import` 布局、文献关联交付和新增数学证明。无截断原生代数、全局分次 presentation 及局部证书迁入主库；通用 Leibniz、Mahowald 和有限 stretching 规则位于 `Def/Kervaire/Route/Tools/`，供 Interface 与 Main 共同使用。stretching 的实际同商障碍条件及其与旧普通 crossing 条件的比较责任保持明确。

独立 `Lin-program/` 研究树不进入本仓源码或构建依赖。现用原始数据库归档保留在 `Source/LWXMachine/kervaire_database.rar`，原始 DB/CSV 与有限重建快照保留在 `KIP126/LinProgram/Raw/`。当前确定性重放所需的四份提取记录放在 `KIP126/LinProgram/Generated/Provenance/`；它们是有具体消费者的来源制品，不恢复历史 `docs/audits/` 目录。来源、原始哈希、派生产物和声明绑定统一登记于 `docs/external-inputs.json`。

目录整合、局部数据证书和可重放生成不解除实际模型、比较映射及论文证明的未完成义务。下列数量与检查结果继续只描述初始迁入快照。

## 初始迁入：保留

- 完整 `KIP126/` 与 `KIP126.lean`，包括 109 个 Lean Checks 模块。
- 完整 `MainPaper/`、`Source/` 和 `docs/external-inputs.json`。
- 完整 Blueprint 数学章节、宏及构建配置；仅修改显示名称并移除旧网站链接。
- 固定 Lean/Mathlib/checkdecls/doc-gen4 依赖，独立 API 文档构建配置。
- `LICENSE`、版权/来源标注、Git LFS 配置、项目边界及精简后的代理指导。
- 当前接口说明和输入清单浏览页。
- 核心来源/接口/依赖/数据导入检查及测试；严格最终验收工具 `scripts/Axioms.lean`。

## 初始迁入：留在旧仓库

- `KIPBase/`、`KIPBase.lean`、KIPBase 专用工具和测试。
- `docs/archive/`、`docs/audits/`、`docs/migration/`，旧进度/迁移摘要和日期化复查报告。
- Multica/Euler 初始化、外部审查、自动合并、状态标签和缓存协调设施。
- 旧 CI/性能/文档发布设施的 Python 测试及运行日志。
- Git 历史、旧远程配置、旧构建缓存与生成的网站/PDF。

## 初始迁入：调整

- `lakefile.lean` 只默认构建 KIP126，移除 KIPBase 及其审计目标。
- CI 从 11 个工作流缩减为 1 个、2 个任务，详见 [CI.md](CI.md)。
- scripts 从 59 个受版本管理的文件缩减为 14 个（含云端资源监控）；来源和数学接口测试保留。
- 全部 KIP126 源码、Lin 制品、数学声明、Blueprint 数学内容及证明状态未修改。
- 保留已有 KIPBase 来源注释；删除模块不抹去代码来源或贡献者信息。

## 初始迁入：原始输入

迁入 7 个 Git LFS 实体，共 617.72 MiB。
工作目录中为可读取的实际 DB/CSV；提交中仍使用 LFS 指针，实体存入本仓库 `.git/lfs/objects/`。
每个文件均按旧指针记录的 SHA-256 和长度核对。

本地核对复用了相同依赖版本的编译缓存。依赖目录 `.lake/packages` 与项目编译目录
`.lake/build` 现在均为独立副本，没有通过共享链接或跨仓库硬链接连接旧缓存。
新库的依赖更新、缓存获取和重新构建使用自己的目录。`.lake/` 整体忽略，
不属于 Git 快照；新克隆按 manifest 获取依赖即可。

核对时先阅读根目录 README、PROJECT_BOUNDARY、AGENTS 和本文件；
运行 `bash scripts/check.sh`、`lake build KIP126`、
`bash scripts/check-blueprint-decls.sh` 与 `git lfs fsck`。
这些检查验证结构、制品、编译及声明链接，不认证未完成的数学证明。

## 初始迁入：本地核对结果

- 1552 个 KIP126 Lean 文件与迁移起点逐字节一致，Blueprint 数学章节未改动。
- 26 项来源、113 个来源制品及声明对应检查通过。
- 保留的 107 项 Python 回归/导入测试通过，Blueprint 活跃依赖图检查通过。
- 新配置下 `lake build KIP126` 通过（4311 项构建任务，复用本地缓存）。
- `leanblueprint web` 及 1715 行声明清单的 checkdecls 核对通过。
- 精简 CI 通过 actionlint；新仓库 7 个原始输入的 Git LFS fsck 通过。
- 依赖缓存隔离后，10 项依赖版本、37 个独立文件样本、缓存链接及 Lean 搜索路径核对通过。
- 隔离后 `lake build --no-build KIP126` 确认 4311 项构建任务均为最新状态；没有全量重编译。

远程 CI 通过 GitHub Actions 运行，Lean action 安装工具链，Lake 执行完整构建，
GitHub cache action 按源码内容复用编译缓存；详见 [CI.md](CI.md)。
网站/API 发布地址尚未配置。
