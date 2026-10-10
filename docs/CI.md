# CI 与本地检查

一个 `ci.yml` 工作流，在 PR、main 推送及手动触发时执行两个任务：

1. **Checks**：来源制品摘要与声明对应、接口分层与唯一见证、公理声明位置、
   Blueprint 标签与依赖图、计算导入边界及相应 Python 回归。
2. **Lean and Blueprint**：获取固定 Mathlib 缓存，完整构建 `KIP126`（包含所有 Lean Checks），
   渲染当前 Blueprint 并核对每个链接的 Lean 声明。两个步骤使用同一份编译结果。

CI 使用只读权限，不接入外部审查服务，不自动合并、发布网站或写 PR 标签/评论。
Blueprint 网页和依赖报告作为工作流制品供核对。API 文档、PDF 和性能分析按需手动执行。
固定版本的 Lean action 负责恢复 GitHub 缓存、获取 Mathlib 缓存、运行
`lake build KIP126`，并在构建成功后保存整个 `.lake/`。构建放在 action 内部，
因此保存的缓存包含本次项目编译结果；后续 Blueprint 步骤直接复用该结果。

GitHub 缓存键包含运行平台、架构、`lean-toolchain`、`lake-manifest.json` 和提交标识。
当前提交没有缓存时，action 尝试恢复相同平台、工具链和依赖版本下的旧缓存；
每次仍执行构建，由 Lake 判断需要重编译的模块。首次运行、缓存被清理或环境变化时，
可能需要重新编译。PR 可以读取 main 的缓存；PR 专属缓存不能被 main 或其他 PR 读取。
本地 `.lake/` 不提交到 Git，也不会自动上传到 CI。

缓存使用 action 的内置流程，不额外引入跨工作流缓存协调机制。
私仓的 Lean 任务设置 `LEAN_NUM_THREADS=1`，以降低首次构建的并行资源占用；
仍完整构建 KIP126 及其 Lean 回归模块。临时 Ubuntu 机器先清理闲置的 .NET 和 Android 工具，
为 Lean 编译产物和缓存打包留出空间。任务记录 CPU、内存、磁盘及工作目录内的 Lean 进程；
内存可用量连续两次低于 512 MiB 或磁盘空闲连续两次低于 1 GiB 时，中止该目录的 Lean 构建，
让资源不足成为可诊断的失败。采样仅在 GitHub Actions 持续运行，诊断制品保留 7 天。

移除旧仓库的自动合并、合并队列协调、外部审查派发、状态标签、旧迁移检查、
专用性能工作流和上述设施的 Python 测试。保留全部数学 Lean 回归模块。

本地运行 `bash scripts/check.sh`，再运行 `lake build KIP126` 和
`bash scripts/check-blueprint-decls.sh`。Blueprint 依赖需先按 README 安装。
`git lfs fsck` 可检查已提交原始输入的 LFS 对象。

编译允许现有未完成证明；来源和接口检查不证明引用的数学内容。
最终验收仍遵守 `PROJECT_BOUNDARY.md`，严格公理审计可通过 `lake exe axioms` 单独执行。
