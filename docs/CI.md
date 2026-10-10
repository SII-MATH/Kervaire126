# CI 与本地检查

一个 `ci.yml` 工作流，在 PR、main/develop 推送及手动触发时执行两个任务：

1. **Checks**：来源制品摘要与声明对应、接口分层与唯一见证、公理声明位置、
   Blueprint 标签与依赖图、计算导入边界及相应 Python 回归。
2. **Lean and Blueprint**：获取固定 Mathlib 缓存，完整构建 `KIP126`（包含所有 Lean Checks），
   渲染当前 Blueprint 并核对每个链接的 Lean 声明。两个步骤使用同一份编译结果。

CI 使用只读权限，不接入外部审查服务，不自动合并、发布网站或写 PR 标签/评论。
Blueprint 网页和依赖报告作为工作流制品供核对，保留 7 天。API 文档、PDF 和性能分析按需手动执行。
固定版本的 Lean action 负责恢复 GitHub 缓存、获取 Mathlib 缓存、运行
`lake build KIP126`，并在构建成功后保存整个 `.lake/`。构建放在 action 内部，
因此保存的缓存包含本次项目编译结果；后续 Blueprint 步骤直接复用该结果。

GitHub 缓存键包含运行平台、架构、`lean-toolchain`、`lake-manifest.json` 和提交标识。
当前提交没有缓存时，action 尝试恢复相同平台、工具链和依赖版本下的旧缓存；
每次仍执行构建，由 Lake 判断需要重编译的模块。首次运行、缓存被清理或环境变化时，
可能需要重新编译。PR 可以读取 main 的缓存；PR 专属缓存不能被 main 或其他 PR 读取。
本地 `.lake/` 不提交到 Git，也不会自动上传到 CI。

GitHub 默认每仓库缓存上限为 10 GB；超过 7 天未访问的缓存会被清理，
达到容量上限时优先清理最近访问时间最早的条目。缓存不是长期存档，
因此必须保留完整冷构建能力。缓存空间与工作流制品空间分别计算。
参见 [GitHub 缓存规则](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching)。

仓库现为公仓，使用标准 `ubuntu-24.04` runner（4 vCPU、16 GB 内存）。
这类公仓 runner 免费且不限 Actions 分钟，不占用组织私仓的月度分钟额度。
私仓同名 runner 为 2 vCPU、8 GB 内存，此前冷构建中生成的有限证书耗尽了
默认内存和交换空间；补足交换空间后，构建仍十分缓慢，因此改用公仓。
参见 [GitHub runner 规格与计费](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)。

Git LFS 存储与下载仍单独计量，公仓也不例外。当前原始输入合计约 0.603 GiB，
Lean 任务完整检出会下载这些输入；组织的共享 LFS 配额需要单独关注。
参见 [Git LFS 计费](https://docs.github.com/en/billing/concepts/product-billing/git-lfs)。

缓存使用 action 的内置流程，不额外引入跨工作流缓存协调机制。
Lean 任务设置 `LEAN_NUM_THREADS=1`，以降低大规模生成证书的并行内存占用；
仍完整构建 KIP126 及其 Lean 回归模块。临时 Ubuntu 机器先清理闲置的 .NET 和 Android 工具，
为 Lean 编译产物和缓存打包留出空间，并增加 8 GiB 交换空间，供生成的有限证书冷构建使用。
任务记录 CPU、内存、交换空间、磁盘及工作目录内的 Lean 进程；
可用内存与空闲交换空间均连续两次低于 512 MiB，或磁盘空闲连续两次低于 1 GiB 时，
中止该目录的 Lean 构建，
让资源不足成为可诊断的失败。采样仅在 GitHub Actions 持续运行，诊断制品保留 7 天。

旧仓库的自动合并、合并队列协调、外部审查派发、状态标签、旧迁移检查和
专用性能工作流归档于 `docs/archive/workflows/`，不在本仓执行。相关 Python 测试
保留作历史参考，不纳入当前检查入口；它们仍假设旧工作流位于原路径。
保留全部 KIP126 数学 Lean 回归模块。KIPBase 及其专用迁移测试、审计工具
按远程状态移除，不属于当前源码树或 CI 构建目标。

本地运行 `bash scripts/check.sh`，再运行 `lake build KIP126` 和
`bash scripts/check-blueprint-decls.sh`。Blueprint 依赖需先按 README 安装。
`git lfs fsck` 可检查已提交原始输入的 LFS 对象。

编译允许现有未完成证明；来源和接口检查不证明引用的数学内容。
最终验收仍遵守 `PROJECT_BOUNDARY.md`，严格公理审计可通过 `lake exe axioms` 单独执行。
