# CI 与本地检查

一个 `ci.yml` 工作流，在 PR、main 推送及手动触发时执行两个任务：

1. **Checks**：来源制品摘要与声明对应、接口分层与唯一见证、公理声明位置、
   Blueprint 标签与依赖图、计算导入边界及相应 Python 回归。
2. **Lean and Blueprint**：获取固定 Mathlib 缓存，完整构建 `KIP126`（包含所有 Lean Checks），
   渲染当前 Blueprint 并核对每个链接的 Lean 声明。两个步骤使用同一份编译结果。

CI 使用只读权限，不接入外部审查服务，不自动合并、发布网站或写 PR 标签/评论。
Blueprint 网页和依赖报告作为工作流制品供核对。API 文档、PDF 和性能分析按需手动执行。
固定依赖缓存由 Lean action 获取；本项目的编译结果不使用跨工作流缓存协调机制。

移除旧仓库的自动合并、合并队列协调、外部审查派发、状态标签、旧迁移检查、
专用性能工作流和上述设施的 Python 测试。保留全部数学 Lean 回归模块。

本地运行 `bash scripts/check.sh`，再运行 `lake build KIP126` 和
`bash scripts/check-blueprint-decls.sh`。Blueprint 依赖需先按 README 安装。
`git lfs fsck` 可检查已提交原始输入的 LFS 对象。

编译允许现有未完成证明；来源和接口检查不证明引用的数学内容。
最终验收仍遵守 `PROJECT_BOUNDARY.md`，严格公理审计可通过 `lake exe axioms` 单独执行。
