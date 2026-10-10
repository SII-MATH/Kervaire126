# 仓库起点与核对清单

当前 Lin 证书工作的模块归属见
[任务归属与继续开发入口](../KIP126/LinProgram/README.md#任务归属与继续开发入口)。
该入口区分已有文件与规划位置，并将 Blueprint 中 P 的六步构造对应到实现层。
本文件下文保留仓库迁移历史，历史文件数量不作为当前目录说明。

Kervaire126 从旧仓库 `SII-MATH/KIP126` 的 main 提取，起点提交：
`9d2601af4529ebcdd353ccc01fe09e0a463ed25a`（PR #157 的合并结果）。
旧仓库与 Git 历史保留；新仓库采用独立初始提交。Lean 包及公共命名空间保持 `KIP126`。
远程仓库为 [SII-MATH/Kervaire126](https://github.com/SII-MATH/Kervaire126)，当前为公开仓库。
Blueprint 尚未配置远程网站/API 链接。

以下迁入清单和本地核对结果记录新仓初始快照；`develop` 后续整合见下一节，
初始文件数量与核对结果不代表合并后的当前状态。

## 主线证书模块归属（2026-10-10）

`Lin-program/` 保持独立。主线原来从该目录使用的 20 个证书模块及其完整
依赖闭包，已复制到 `KIP126/LinProgram/Certificates/` 和 `Tactic/`，由 KIP126
维护。根 Lake 配置不再注册该独立目录；四处主线导入改为 KIP126 模块路径。
原始研究 Lean 源码保持不变，仅在其 README 增加主线导航；未增加共享包，也未将其余实验和生成批次纳入主线。

来源提交、目录对应及职责见
[LinProgram README](../KIP126/LinProgram/README.md#independence-from-the-research-attempt)。
此次归属调整保留公开声明名、定理内容、输入制品和证明状态；不构造实际
E₂ 比较，也不增加已经认证的 Adams 微分。

## develop 本地进展整合（2026-10-10）

- 合并旧仓本地开发历史与 Kervaire126 更新，保留本地 KIP126 证明进展。
- KIPBase 按远程 `develop` 状态处理：移除 `KIPBase/`、`KIPBase.lean`、
  专用脚本、测试、进展清单及 `docs/migration/kip-base/` 迁移档案；
  不恢复 `KIPBase` 和 `kipbaseAudit` 构建目标。相关本地进展仍保留在合并前提交中。
- 保留通用 `docs/archive/`、`docs/audits/`、其余迁移文档和旧工具作为开发历史。
  历史报告、测试与旧仓配置不代表本仓当前 CI 或已完成证明。
- 采用新仓精简 `ci.yml`，增加 `develop` 推送触发；
  旧仓的 10 个其他工作流原样移至 [archive/workflows/](archive/workflows/)，
  不再作为 GitHub Actions 工作流执行，不恢复旧自动合并、外部审查或网站发布。
- 旧工作流测试仍保留其原路径假设，供历史参考，不纳入 `scripts/check.sh`。
  当前验证入口为本仓的来源、接口、Blueprint 检查和各库的显式构建。

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

远程 CI 通过 GitHub Actions 运行，构建缓存由 Lean action 管理；详见 [CI.md](CI.md)。
网站/API 发布地址尚未配置。
