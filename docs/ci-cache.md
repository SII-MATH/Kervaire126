# CI 缓存维护

实现入口是 [CI 工作流](../.github/workflows/ci.yml) 和
[`ci_build_artifact.py`](../scripts/ci_build_artifact.py)。缓存用于复用编译产物；每次仍运行
`lake build KIP126 checkdecls`、来源与接口回归、Blueprint 渲染及声明核对。
缓存命中和制品校验均不代表数学证明完成，验收边界仍见
[`PROJECT_BOUNDARY.md`](../PROJECT_BOUNDARY.md)。

## 同分支构建与失败续建

GitHub Actions cache 保存整个 `.lake/`，仍受分支和 PR 的可见范围限制。
PR 专属缓存不能直接作为合并后 `main` / `develop` 的分支缓存。
键前缀绑定平台、架构、`lean-toolchain` 和 `lake-manifest.json`；
`fingerprint` 绑定全部已跟踪 Git 树，因此文档、CI 和辅助脚本的变化也会改变它。

- 完整构建键：`…-build-v3-<fingerprint>-complete`。完整 Lean 构建成功后、
  Blueprint 检查前保存；这里的 `complete` 指 Lean 构建，不表示整个 CI 已通过。
- 失败进度键：`…-build-v3-<fingerprint>-progress-<run_id>-<run_attempt>`。
  构建失败或取消后，若已有项目 trace，则尽力保存已完成的模块。
  Actions cache 不可覆盖；每次尝试使用唯一键，避免旧进度阻止更新。
- 恢复顺序：精确 `complete` → 同 fingerprint 的缓存 → 同平台、工具链与依赖的
  `build-v3` 缓存 → 旧 `sources-v2` 缓存 → 更早兼容前缀。
  Lake 根据当前输入和 trace 决定哪些产物可复用，其余仍编译。

Lean 构建步骤上限为 105 分钟，整个任务为 135 分钟，给保存缓存等收尾步骤留出时间。
缓存保存步骤各限 8 分钟；可选的合并制品恢复和上传各限 5 分钟，打包限 10 分钟，失败不阻断正常检查。
这些步骤的上限不能累加到 135 分钟之外，前置环境准备也占用总预算。
105 分钟构建上限是在继续本次编译与保存进度之间的主动取舍，不是可靠的硬取消保存承诺。
硬取消、runner 丢失、磁盘或网络故障仍可能丢失本次进度；保存缓存失败不会改变 Lean 构建本身的结果。

## 合并后复用成功 PR 的编译产物

同仓库、非 fork PR 在 Lean 和 Blueprint 步骤成功后，打包 `.lake/build/`
为 `project-build.tar.gz`，并附 `metadata.json`，上传 `lean-build-v1-<fingerprint>-<OS>-<arch>` 制品，保留 3 天。
跨合并传递的范围只有项目构建目录；外部依赖仍通过上述 `.lake/` 缓存和固定 Mathlib
缓存恢复。接收方只接受整个 CI workflow run 已成功的制品。

`main` / `develop` 的 push 未精确命中完整缓存时，尝试恢复该提交对应的已合并 PR 制品。
恢复工具核对 PR 确已合并、merge SHA 等于当前 SHA、同仓库非 fork 来源、指定 CI workflow
及其成功 run；再核对平台、工具链、依赖、完整 Git 树 fingerprint 和压缩包摘要。
解包前还检查路径和条目类型，拒绝越界写入。任一校验失败都放弃此制品，继续正常构建。
该流程只需 `actions: read`，不授予仓库写权限，也不使用 `pull_request_target`。

此机制不保证合并后零编译。PR 基于旧 base、最终合并树不同、制品到期或不存在、下载失败时，
会正常退回可用缓存和构建。新策略部署前已经运行的旧 job 不会补发制品；
过渡阶段的一次合并仍可能需要重新编译。源码或依赖确有变化时也必须重新检查。

## 排查与本地回归

先看 `Restore compiled Lean dependencies and project` 的匹配键和 `cache-hit`：
只有精确命中当前 `complete` 键才是精确命中，恢复旧键仍需要构建。
再看 `Reuse the successful PR build after merging`：成功日志为
`Restored project build from successful PR run ...; Lake will recheck it.`，
未恢复时输出 `::warning::` 原因，并记录 `restored=false`。
合并制品缺失时，到原 PR run 查看打包、上传步骤及制品是否过期。

构建失败后，查看 `Preserve completed modules after a failed build` 是否保存了本次
`run_id` / `run_attempt` 的进度键。资源不足的线索在 `lean-resources` 制品的
`lean-resources.log`；Blueprint 环境安装另有 `blueprint-setup.log`。
缓存上传成功不会把失败的 CI 变成成功，下一次仍须通过全部检查。

在仓库根目录执行：

```sh
python3 scripts/ci_build_artifact.py fingerprint
python3 -m unittest scripts.test_ci_build_artifact
bash scripts/check.sh
lake build KIP126 checkdecls
bash scripts/check-blueprint-decls.sh
```

前两项用于检查输入身份及制品恢复边界，后面三项重放项目的完整检查流程。
运行完整来源检查前应已取得固定 LFS 输入，Blueprint 环境按 [CI 与本地检查](CI.md) 配置。
