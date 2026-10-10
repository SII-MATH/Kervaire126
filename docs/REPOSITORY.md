# 仓库起点与核对清单

Kervaire126 从旧仓库 `SII-MATH/KIP126` 的 main 提取，起点提交：
`9d2601af4529ebcdd353ccc01fe09e0a463ed25a`（PR #157 的合并结果）。
旧仓库与 Git 历史保留；新仓库采用独立初始提交。Lean 包及公共命名空间保持 `KIP126`。
当前还没有远程仓库，Blueprint 未配置远程网站/API 链接。

## 保留

- 完整 `KIP126/` 与 `KIP126.lean`，包括 109 个 Lean Checks 模块。
- 完整 `MainPaper/`、`Source/` 和 `docs/external-inputs.json`。
- 完整 Blueprint 数学章节、宏及构建配置；仅修改显示名称并移除旧网站链接。
- 固定 Lean/Mathlib/checkdecls/doc-gen4 依赖，独立 API 文档构建配置。
- `LICENSE`、版权/来源标注、Git LFS 配置、项目边界及精简后的代理指导。
- 当前接口说明和输入清单浏览页。
- 核心来源/接口/依赖/数据导入检查及测试；严格最终验收工具 `scripts/Axioms.lean`。

## 留在旧仓库

- `KIPBase/`、`KIPBase.lean`、KIPBase 专用工具和测试。
- `docs/archive/`、`docs/audits/`、`docs/migration/`，旧进度/迁移摘要和日期化复查报告。
- Multica/Euler 初始化、外部审查、自动合并、状态标签和缓存协调设施。
- 旧 CI/性能/文档发布设施的 Python 测试及运行日志。
- Git 历史、旧远程配置、旧构建缓存与生成的网站/PDF。

## 调整

- `lakefile.lean` 只默认构建 KIP126，移除 KIPBase 及其审计目标。
- CI 从 11 个工作流缩减为 1 个、2 个任务，详见 [CI.md](CI.md)。
- scripts 从 59 个受版本管理的文件缩减为 13 个；来源和数学接口测试保留。
- 全部 KIP126 源码、Lin 制品、数学声明、Blueprint 数学内容及证明状态未修改。
- 保留已有 KIPBase 来源注释；删除模块不抹去代码来源或贡献者信息。

## 原始输入

迁入 7 个 Git LFS 实体，共 617.72 MiB。
工作目录中为可读取的实际 DB/CSV；提交中仍使用 LFS 指针，实体存入本仓库 `.git/lfs/objects/`。
每个文件均按旧指针记录的 SHA-256 和长度核对。

本地核对复用了相同依赖版本的编译缓存；`.lake/packages` 是指向旧仓库依赖缓存的本地链接，
`.lake/` 整体忽略，不属于 Git 快照。新克隆按 manifest 获取依赖即可。

核对时先阅读根目录 README、PROJECT_BOUNDARY、AGENTS 和本文件；
运行 `bash scripts/check.sh`、`lake build KIP126`、
`bash scripts/check-blueprint-decls.sh` 与 `git lfs fsck`。
这些检查验证结构、制品、编译及声明链接，不认证未完成的数学证明。

## 本地核对结果

- 1552 个 KIP126 Lean 文件与迁移起点逐字节一致，Blueprint 数学章节未改动。
- 26 项来源、113 个来源制品及声明对应检查通过。
- 保留的 107 项 Python 回归/导入测试通过，Blueprint 活跃依赖图检查通过。
- 新配置下 `lake build KIP126` 通过（4311 项构建任务，复用本地缓存）。
- `leanblueprint web` 及 1715 行声明清单的 checkdecls 核对通过。
- 精简 CI 通过 actionlint；新仓库 7 个原始输入的 Git LFS fsck 通过。

远程 CI 尚未运行，网站/API 发布地址尚未配置；本次只建立本地可核对的仓库。
