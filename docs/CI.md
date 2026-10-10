# CI 与本地检查

一个 `ci.yml` 工作流，在 PR、main/develop 推送及手动触发时执行两个任务：

1. **Checks**：下载并校验固定 LFS 原始输入，检查来源制品摘要与声明对应、接口分层与唯一见证、公理声明位置、
   Blueprint 标签与依赖图、计算导入边界及相应 Python 回归。
2. **Lean and Blueprint**：获取固定 Mathlib 缓存，完整构建 `KIP126`（包含所有 Lean Checks），
   渲染当前 Blueprint 并核对每个链接的 Lean 声明。两个步骤使用同一份编译结果。

CI 使用只读权限，不接入外部审查服务，不自动合并、发布网站或写 PR 标签/评论。
Blueprint 网页和依赖报告作为工作流制品供核对，保留 7 天。API 文档、PDF 和性能分析按需手动执行。
固定版本的 Lean action 负责安装 Lean 环境，随后显式运行
`lake build KIP126 checkdecls`。GitHub cache restore/save 步骤管理
整个 `.lake/`；完整构建和 Blueprint 声明核对成功后才保存，包含声明检查器的编译结果。
每次都执行完整构建和声明核对，由 Lake 决定哪些模块需要重编译。

GitHub 缓存键包含运行平台、架构、`lean-toolchain`、`lake-manifest.json`，以及项目
Lean 源码、Lake 配置和 Lean 脚本的内容摘要。仅修改文档或 CI、Lean 输入不变时，
直接命中已有缓存并省去再次打包上传；源码变化时恢复同工具链、同依赖的旧缓存，
完成增量构建后保存新缓存。恢复前缀兼容此前 Lean action 保存的缓存。
精确命中成功构建缓存后，省去重复执行 Mathlib 缓存下载器。
未精确命中时，`scripts/mathlib-cache-roots.py` 用 Lean 内建的 `--deps-json` 解析
所有已跟踪 Lean 源文件的导入，再由官方 `lake exe cache get` 获取这些外部模块及
完整传递依赖。缓存不再包含项目没有使用的整份 Mathlib；迁移旧缓存时只清掉
旧 Mathlib 模块产物并重新获取所需部分，保留项目编译结果和缓存工具。
`MATHLIB_NO_CACHE_ON_UPDATE=1` 防止依赖初始化时自动下载全库。
缓存键还包含上述依赖选择脚本，脚本变更也会触发更新。
首次运行、缓存被清理或环境变化时，
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
Checks 任务完整检出会下载这些输入；Lean 编译使用已提交的生成数据，检出时保留 LFS 指针。
两个任务并行执行，原始输入下载和校验不再延长 Lean 任务。组织的共享 LFS 配额需要单独关注。
参见 [Git LFS 计费](https://docs.github.com/en/billing/concepts/product-billing/git-lfs)。

缓存使用 GitHub 官方 cache action；完整构建由 Lake 执行。
Lean 任务设置 `LEAN_NUM_THREADS=2`，利用公仓 CPU 并限制大规模生成证书的并行内存占用；
仍完整构建 KIP126 及其 Lean 回归模块。临时 Ubuntu 机器只有在可用磁盘不足 40 GiB 时
才清理闲置的 .NET 和 Android 工具，并增加 8 GiB 交换空间，供生成的有限证书冷构建使用。
Blueprint 网页使用 MathJax，安装 Graphviz、Python 渲染依赖及提供 `kpsewhich` 的
`texlive-binaries`。`kpsewhich` 用于找到嵌套的 TeX 源文件；CI 不安装 LaTeX 格式包、
Ghostscript 或 PDF 转换工具。渲染步骤显式设置 `TEXINPUTS=.:`，使精简环境也能找到
当前目录下的主文件和嵌套章节，不依赖完整 TeX 安装提供的搜索路径默认值。
Blueprint 环境安装与 Lean 缓存恢复并行；安装结果在开始 Lean 编译前核对，
安装失败仍使任务失败，日志保留在对应步骤中。
Lean 任务上限为 120 分钟，以容纳首次或缓存被清理后的完整冷构建。
首次公仓试运行确认 16 GB 内存充足，但先前沿用的单线程配置在 90 分钟上限前
只完成 1331 个 KIP126 模块；7 个平方检测证书批次串行编译共约 24 分钟。
因此使用两个工作线程，并保留资源监控。此试运行没有完成全库构建或保存项目缓存。

任务记录 CPU、内存、交换空间、磁盘及工作目录内的 Lean 进程；
可用内存与空闲交换空间均连续两次低于 512 MiB，或磁盘空闲连续两次低于 1 GiB 时，
中止该目录的 Lean 构建，
让资源不足成为可诊断的失败。采样仅在 GitHub Actions 持续运行，诊断制品保留 7 天。

## 云端实测

2026-10-10，公仓 PR #1 在两个工作线程下完成首次项目冷构建：

| 项目 | 实测 |
| --- | --- |
| `lake build KIP126` | 41 分 52 秒 |
| Lean and Blueprint 整个任务 | 49 分 02 秒 |
| 首次编译的 KIP126 模块 | 1552 个（含全部 Lean Checks） |
| 完整构建任务 | 4311 项 |
| 保存的 `.lake/` 缓存 | 约 2.7 GiB（压缩后） |

此运行没有项目缓存，使用固定依赖的上游 Mathlib 缓存。完整库构建、Blueprint
渲染与声明核对均通过；资源采样确认最多两个 Lean 编译进程同时运行，
最低可用内存约 4.1 GiB，交换空间最高使用 49 MiB。
这是 CI 编译与检查结果，数学证明的验收仍遵守项目边界。

[实测运行](https://github.com/SII-MATH/Kervaire126/actions/runs/38041208111)。
这份缓存属于 PR #1；合并后的 main 需要建立自己的缓存。

优化前，同日一次仅修改文档的
[热缓存运行](https://github.com/SII-MATH/Kervaire126/actions/runs/38044227897)
未重编译任何 KIP126 模块，`lake build KIP126` 用时 2.6 秒，但整个 Lean and Blueprint
任务仍用时 5 分 23 秒。主要额外开销为固定磁盘清理、完整缓存再次上传、LFS 下载和
Blueprint 环境安装，以上缓存与环境配置针对这些开销做了调整。

[精简依赖缓存的迁移验证](https://github.com/SII-MATH/Kervaire126/actions/runs/38046922617)
完整通过，Lean and Blueprint 用时 3 分 08 秒，包含旧缓存恢复、一次性清理和新缓存保存；
并行 Checks 用时 1 分 24 秒。Lean 原生解析器找到 151 个直接外部导入，官方缓存工具
获取其 2743 个依赖产物；全部 4315 项构建任务通过，项目模块零重编译。
压缩缓存由 2,968,087,199 字节缩到 1,746,694,930 字节（约 2.76 GiB → 1.63 GiB）。
后续 Lean 输入不变的提交精确命中同一缓存，不再清理、补取或重复保存。
两分钟目标针对可复用编译结果的日常运行；首次冷构建或大型证明修改仍需实际编译时间。

移除旧仓库的自动合并、合并队列协调、外部审查派发、状态标签、旧迁移检查、
专用性能工作流和上述设施的 Python 测试。保留全部数学 Lean 回归模块。

本地运行 `bash scripts/check.sh`，再运行 `lake build KIP126` 和
`bash scripts/check-blueprint-decls.sh`。Blueprint 依赖需先按 README 安装。
`git lfs fsck` 可检查已提交原始输入的 LFS 对象。

编译允许现有未完成证明；来源和接口检查不证明引用的数学内容。
最终验收仍遵守 `PROJECT_BOUNDARY.md`，严格公理审计可通过 `lake exe axioms` 单独执行。
