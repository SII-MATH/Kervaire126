# 最新实现整理 — 2026-10-13

分支：`codex/local-backup-20261013`。当前仓库的实际 Lean 源码是唯一采用版本；
这里不再放置与它并列的候选实现。`main`、`develop` 和两个原仓库均未改动。

## 取舍结果

| 范围 | 当前采用的实现 |
| --- | --- |
| Main 的 generalized Mahowald | 合入原 KIP126 工作区较新的完整假设与具体见证包，共 11 个辅助声明；定理类型不变，原有 `sorry` 保留。 |
| Adams–Bockstein | 保留 10 月 13 日的 E₂ 比较、Zᵢ/Bᵢ 逐页商归纳；不恢复较旧的关系判据唯一路线。 |
| KIPBase 的 generalized rules | 保留当前同步代表元、共同商提升及实际像等式；不恢复任意命题占位或旧的独立 May-lift 输入路线。 |
| 过滤复形、交换性 | 保留当前集成接口及有界/无界交换性模块；不恢复旧包装模块和已退役接口。 |
| Blueprint | 只采用根目录 Blueprint，且同步上述新增声明；嵌套副本和生成网页不作为第二份实现。 |

重建时还删除了 `LambdaBoundary.lean` 中一条已无目标可处理的冗余 `congr 1`。
前一步已完成证明；定理类型、假设和所采用的路线均未改变。

独立 KIP-base 的 `FilteredComplexNaturality.lean` 是尚未移植的独有草稿：
它依赖当前已不存在的接口，不能直接编译接入。其内容完整留在历史区；
这不表示其中所有数学结论已经被新版吸收，也不为接入它而恢复旧架构。
稳定模型结构、三角范畴相关文件继续保留当前 KIPBase 版本；没有把其中的
输入假设或公理改称为已完成的证明。

## 防遗漏与历史恢复

`selection.json` 逐项记录两个原仓库的全部 **121 个改动路径（55 + 66）**、
原始摘要、处理方式、采用源码的位置及摘要。`verify_selection.py` 检查其覆盖范围。
它记录的是本次选择时的源码快照；以后继续开发时需要重新核对并更新摘要。
另核对了本地独有的 `codex/lambda-quotient-tower-proof` 分支：它改动的 41 个
KIPBase Lean 文件在当前源码中全部存在，其中 23 个内容相同，18 个保留当前
进一步开发的版本；没有为恢复旧分支而倒退现有接口。该比较也记录在清单中。

`history/` 仅用于恢复，不是当前开发的候选源码目录。它完整保留两个原仓库的
改动文件、补丁、索引状态及全部 **5 个本地分支**，包括未被远程吸收的提交。
历史内容与完整备份提交 `c0bad770ae75dde7ca8778040658ee4d381a095d` 一致，
只移动了存放位置，没有删除旧工作。原始捕获说明见 `history/README.md`。

从仓库根目录验证：

```sh
python3 backups/local-20261013/verify_selection.py
python3 backups/local-20261013/history/restore.py KIP126 --verify-only
python3 backups/local-20261013/history/restore.py KIP-base --verify-only
```

恢复到全新目录（Python 3.12+ 和 Git）：

```sh
python3 backups/local-20261013/history/restore.py KIP126 --destination /new/empty/location/KIP126
python3 backups/local-20261013/history/restore.py KIP-base --destination /new/empty/location/KIP-base
```

恢复工具不会推送远程，也不会覆盖已存在的目录。

## 证明与检查边界

本次整理不改变 Challenge2、不新增公理，也不补齐 Mahowald 最终证明。
源码编译、选择清单校验与历史恢复成功不等于数学证明完成。
Blueprint 保留 `\notready`，明确见证提取不证明同步代表元、共同提升或更强生存。

已通过的检查：

- 更新后的 Main Mahowald、λ 边界模块及已有 Section7 模块编译。
- Mahowald 最终声明与原 `GeneralizedMahowaldLaw` 的类型相容性检查；
  五个辅助构造只依赖 Lean 的标准逻辑公理，最终定理仍依赖 `sorryAx`。
- 固定版本 `leanblueprint 0.0.20` 网页渲染、活动标签/依赖检查、来源清单与外部输入检查。
- 外部输入和 Blueprint 的 61 项测试、输入转换的 6 + 7 项测试。
- 全部 121 个路径、63 个选定文件摘要、本地独有分支的 41 个 Lean 文件校验；
  防漏项、重复项、错误摘要及错误分支位置的 6 项反向测试。
- 两份历史档案完整性校验、43 个归档文件与原完整备份逐字节一致；
  两个原仓库的工作区、索引与所有本地分支位置未变。

综合测试发现的既有问题另行保留，不通过改弱检查来消除：

- KIPBase 入口的重新编译未通过：未修改的
  `Synthetic/AdamsBocksteinMorphism.lean` 从第 110 行起缺少
  `SyntheticModelRealizationWitness Syn`，随后有连锁错误及冗余证明步骤。
  本次保留最新 Zᵢ/Bᵢ 路线，不通过新增公理、全局实例或修改公共假设绕过错误。
  完整 Blueprint 编译声明检查也未通过，原缓存中缺少 6 个新版 KIPBase 声明；
  网页渲染成功不代表该检查成功。此接口迁移需要单独处理。
- 公理边界测试发现 `Section7.lean` 的 `compositionOnlyMossInterface` 和
  `Def/Kervaire/Route/Massey/Axioms.lean` 的 `e2_massey_page3_representation`；
  两个文件在本次整理前已存在且未修改，仍违反现有单一项目公理规则。
- 当前 Python 3.13 下，来源清单的符号链接循环诊断测试失败；
  来源清单本身及外部输入校验通过。相关脚本未修改。
