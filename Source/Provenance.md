# 来源与制品管理

[docs/external-inputs.json](../docs/external-inputs.json) 是唯一机器清单：来源身份、locator、获取状态、制品摘要、Lean 声明与 Blueprint 标签以及路线审计项都在这里维护。原 source-inventory 和 route-sources 两份 JSON 已合并；没有 Lean 来源投影或 claim registry。

Lean 数学字段直接接收命题或认证数据。文献、计算、模型比较和内部推导保留各自角色；引用 metadata 不再通过 `ExternalResult`、`ExternalEvidence` 或 `SourceId` 进入接口。

主论文在 [MainPaper](../MainPaper/)，外部文献制品在本目录；各作品的 `source-status.json` 保存原始获取记录。固定 Lin 数据仍由 `KIP126/LinProgram/Raw/` 保存。Git LFS pointer 不能冒充输入实体。

`python3 scripts/check_source_inventory.py` 检查来源、路径、状态和摘要；`python3 scripts/check_external_inputs.py` 检查声明、角色和定位关系。检查通过不证明原文蕴含 Lean 命题，也不意味着计算已认证。

固定球谱基础适用性与滤过分离性在 Def 中以未完成证明的定理明确陈述；固定路线、模型与共享数学背景也由 Def 确定。`Challenge2` 顶层只交付 `literature` 与 `computation`：两包各自带有 `bindings` 和依赖其绑定的 `results`，计算包还依赖同一文献包。内部应用是 Main 的待证目标。来源到所选模型的识别责任不能被省略。

当前文献覆盖、部分原文/locator 核验仍有待核验项。C₂/Cη 是 Interface 计算认证可能使用的内部证明依赖，不是 Challenge2 必须交付的字段；计算结论的认证责任仍须完成。详细范围见 [接口说明](../docs/STAGE0_INTERFACES.md)。维护时保留已有来源 ID；新增原文更新 manifest 及获取记录，数学陈述核验与文件摘要检查分别完成。
