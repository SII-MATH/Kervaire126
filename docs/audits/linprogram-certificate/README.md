# Lin 原生证书执行记录

日期：2026-10-09。工作分支：`codex/linprogram-certificate`。
工作区：`/inspire/hdd/global_user/czxs25250150/linprogram-certificate`。

本记录按用户明确要求的依赖顺序推进。所引用 Page 的 P0–P7 正文尚未能从当前会话读取，已请求正文；以下里程碑不是对未读取的分期验收条款的复述。旧 issue152 工作以现有模块复用，本次新增结果分别核验。

迁移前最新状态见文末“分支迁移交接（2026-10-10）”；前文批次进度为历史记录。

## 固定原生输入与 statement 合同

`KIP126/LinProgram/Raw/manifest.json` 保留原始数据库/CSV 的固定摘要，并纳入 `ss.json` 在既有 `select-route.py` 中已经固定的 SHA256：
`a9a623bf7165e62fcf455e454fdf9195237491bf07bd148902e245aa1dba64d8`。
其来源仍登记在唯一 canonical manifest `docs/external-inputs.json` 的既有 `lwx_machine` 条目下。

确定性 `Translate/native-contract.py` 输出
`Generated/NativeContract/manifest.json`，固定原始行、字段、坐标、辅助多项式见证及缺失依赖。462481 条目已更新为原生上下文已找回，保持实际认证为 false，并链接可重建快照；连续 N→N 的来源标签和剩余实际义务有专门检查。合同生成前从固定输入完整重建该上下文，逐字比较，不能通过对被删改前提的派生 JSON 重新盖哈希来接受它。它检查输入哈希与提取结果，不宣称完成 Lean 或实际数学认证。

| 原生目标 | 完整数学坐标 | 当前状态 |
| --- | --- | --- |
| 根结论 152098，`D` | S0，`d4:(4,42)[1] → (8,45)[]` | 实际微分待证 |
| 保留 trial 152097，`T` | 相同源，候选目标 `[0]`；诊断得到 `d4:(5,44)[] → (9,47)[0]` | 乘积部分已闭合；分支整体待证 |
| 来源候选 245130，`D` | Ceta，`d3:(2,19)[0] → (5,21)[0]` | 来源微分及原生坐标绑定待证 |
| 自然性 245131，`N` | S0，`d3:(2,17)[0] → (5,19)[0]`，`info=Ceta__S0` | 条件传输；不是实际认证 |

`stem=t-s`，列表索引从零开始。SQL NULL、`-1`/`[null]` 未知值、空字符串零向量严格区分。有限微分页限于 `2 ≤ r < 999`；阈值及到达某页不自动升级为非零永久存活。论文别名不进入这些原生目标。

重放命令（以下均在本工作区执行）：

```sh
python3 KIP126/LinProgram/Translate/native-contract.py --check
python3 KIP126/LinProgram/Translate/test-native-contract.py
python3 KIP126/LinProgram/Translate/test-pinned-inputs.py
```

## 闭合的固定数据商代数证书

使用现有 `KIP126.LinE2.E2`：变量为 `Fin 2914`，系数为 F2，理想含完整归档关系及原有的 `t > 261` 截断。没有另建小型替代代数。

`KIP126.LinE2.ReplayProducts.native_source_product_zero` 证明：

```text
projection (monomialOfString "0,2,1,1,3,1,18,1") = 0
```

`KIP126.LinE2.ReplayProducts.native_target_product` 证明：

```text
projection (monomialOfString "1,1,9,1,13,1") =
projection (monomialOfString "0,3,36,1")
```

对应原生生成元等式为 `x0²*x1*x3*x18=0` 与 `x1*x9*x13=x0³*x36`，次数分别为 `(5,44)` 与 `(9,47)`。

所用 CSV 关系记录序号（零基，不计 header）为 `0,25,187,189`。新 `lin_relation` 战术仅提出原始字符串的分解；Lean 内核通过 `rfl`、`decide +kernel` 和通用成员定理检查它。随后由 `csv_relation_zero` 和环恒等式得到商中的结果。

```sh
lake build KIP126.Checks.AdamsE2.LinReplayProducts
```

检查包括传递公理审计、禁止 Interface/Main 导入、未知关系与错配关系证书拒绝、错误指数不能复用当前证书。最后一项不是证明错误目标在商中不相等。

结果：两条原生定理已单独编译，传递依赖仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx` 或项目公理。这是实际固定数据商的闭合认证；尚不证明球面上的 152098 微分。

`ReplayCoordinates` 进一步把这些等式绑定到四条确切归档行：`(4,42)[1]="0,2,3,1,18,1"`、`(1,2)[0]="1,1"`、`(8,45)[0]="9,1,13,1"`、`(9,47)[0]="0,3,36,1"`。每条行的成员性、商值与同质次数均由 Lean 核查，得到 `source_mul_multiplier : mulAt source dataH1 = 0` 和 `multiplier_mul_trialTarget : mulAt dataH1 trialTarget = productTarget`，公理仅为标准逻辑公理。

`Interface.Solution.LinProgram.ReplayProducts` 通过同一个 `P.comparison_mul` 运输两式。其结论针对该 presentation 的 `P.product`；实际高页球面乘积比较仍待证。它继承现有 `LinE2Presentation` 的固定模型基础依赖，不读取待构造的总交付。

```sh
lake build KIP126.Checks.AdamsE2.LinReplayCoordinates \
  KIP126.Interface.Solution.LinProgram.Products.Trial152097
```

## 真实自然性日志的条件传输

`Raw/Naturality.lean` 保留完整的两条原始行，球面输出以 Lean 定理核对 `RawData.shard51[43]`。`Interface/Solution/LinProgram/Naturality.lean` 使用：

- 同一 `standardRouteModel.auxiliary.etaMap` 的实际余纤维 `Ceta`。
- 实际连接映射 `topCell : Ceta → ΣS1`。
- 已构造的 `adamsInternalE2Induced_hasDifferential`。
- 同一固定 route 的两次 `classicalSuspension`。
- 同一个传入 `LinE2Presentation P` 的源、目标比较。

`row245130_topCell` 给出从实际来源微分到实际 `ΣS1` 像微分的条件定理。`row245131_native` 固定使用 `(2,17)[0]="0,1,7,1"` 和 `(5,19)[0]="0,1,8,1"` 的已构造商元素；两项 `HasCoordinates` 均已证明且无 `sorryAx`，不再是调用方前提。原 `row245131` 保留通用坐标接口。二者结论都是固定原生输出的 `DifferentialStatement P output245131`，额外前提全部显式：

1. `CetaCoordinates` 必须最终被识别为已固定 Ceta 原生数据库的实际坐标；当前函数参数本身不是该识别的证明。
2. `SourceEquation coordinates`：实际 Ceta 上 `(2,19)[0]` 至 `(5,21)[0]` 的 `d3`。
3. 两次降悬各自对源、目标的四条 `DesuspendsClass` 比较。
4. 固定 Def 模型本身的既有基础待证命题仍保留。

此前的 `DoubleDesuspensionCompatible` 前提已解除：`doubleDesuspensionCompatible` 由泛型 `TowerComparison.hasDifferential_desuspendTwice` 实例化同一固定 route 的两份 tower comparison 得到。该泛型定理保留**所有**整数页、次数与代表元量词，从真实单次反交换律证明两负号抵消；固定模型实例仍继承其原有基础义务。

已从本机保存的**同版本原始归档**补入 `Ceta_AdamsSS_t200.db` 和 `map_AdamsSS_Ceta_to_S0_t200.db`。归档为 `kervaire_database.rar`，82746451 字节，MD5 `91ea5d8ef613828b9ef66f6d9f879166`，与既有 `Source/LWXMachine/zenodo-record.json` 核对一致。两份实体的大小、SHA256、归档成员及提取命令均记在同一 canonical manifest；按仓库原有规则存储为 LFS。

原生基底行 id69 为 `7,1,1`、id80 为 `8,1,1`，模块生成元 1 的像为 S0 的 `0,1`。固定 schema 和映射版本元数据后，两个所需局部矩阵都是 `[[1]]`，将两端 `[0]` 精确送到原生日志的 `[0]`。互反 staircase 行也固定在快照中。这是数据库中存储的模块生成元像的形式线性延拓及直接单项式匹配，仍不是实际谱序列映射比较。

相邻日志及这些原生矩阵不提供来源微分的证明。额外目标 462481 的原生源数据和完整上下文已提取并重建，见下节；其实际来源微分及比较仍未认证。来源审计在只存在 LFS 指针时明确报告 metadata-only；`native-contract.py` 必须读取并哈希验证实体字节，不能用指针代替数据核验。原生输入加载器还严格核对指针完整格式、登记 OID 和大小，在构造缓存路径前拒绝畸形或错配指针；7 项实体/指针/缓存回归测试通过。

```sh
lake build KIP126.Checks.AdamsE2.LinNaturalityCoordinates \
  KIP126.Checks.ClassicalAdams.LinNaturalityReplay
```

## 分支规则已闭合的部分

新通用定理 `HasDifferential.isBoundaryBy_of_source_zero` 对任意实际内部谱序列证明：

```text
3 ≤ r → HasDifferential E r p q 0 y → IsBoundaryBy E (r-1) q y
```

其否定推论与 `TrialRefuted.of_zero_source` 保留完整祖先上下文。`LinReplayRules` 对 152097 诊断的精确参数 `r=4,p=(5,44),q=(9,47)` 检查。源代表元由唯一性为零，实际线性微分也为零，实际商页零判据给出早期边界。

```sh
lake build KIP126.Checks.ClassicalAdams.LinReplayRules
```

三个新定理的独立 Lean 编译和传递公理审计已通过，仅使用标准逻辑公理。实际目标的 `¬ IsBoundaryBy ... 3 ...` 仍是数学义务，数据库的文字断言不提供其证明。

## 462481 上游分支的完整原生候选商

`row462481-trace.json` 保留原始 11 列日志、相邻分支、完整局部数据库切片及来源链。462479 是 CW_nu_eta 的 `D`：`d3:(15,144)[1]→(18,146)[0]`；随后 462480 是 Ceta 的 `N`：`d3:(15,140)[1]→(18,142)[0]`，462481 是 S0 的 `N`：`d3:(15,138)[2]→(18,140)[2]`。相邻位置、映射元数据及原生像共同支持这条重构链，但数据库没有显式 parent-id 列；不能把重构边当成已证数学依赖。

`LinProgram.BranchD2Coordinates.kernel_mod_image_representatives` 对所有 `Fin 4 → F2` 向量证明完整核/像商的唯一代表为 `[]、[0]、[2]、[0,2]`。原矩阵是 5→4→4：入射列 `[1,3],[],[],[],[]`，出射列 `[],[2],[],[2]`，对应全部原始行 `5600–5604 → 5720–5723 → 5854–5857`。没有丢弃零列或把未知列当成零。核有八个元素，像有两个元素；定理保留全部五维入射域和四维中间域。

这一步只认证实际固定原生矩阵的线性代数。它不提供实际 CW 的 E2 比较、实际 d2 交换方块或实际 E3 `CandidateCoverage`，也没有把三条 trial 的文字诊断升级为反驳证明。

```sh
python3 -B KIP126/LinProgram/Translate/extract-row462481-trace.py --check
python3 KIP126/LinProgram/Translate/check-branch-d2-coordinates.py
python3 KIP126/LinProgram/Translate/test-branch-d2-coordinates.py
lake build +KIP126.Checks.AdamsE2.LinBranchD2Coordinates:olean
```

独立 Lean 编译、公理/导入审计及 8 项数据负例通过。证明只使用标准逻辑公理。只读检查从唯一 canonical 清单中既有 Zenodo 记录摘要出发，认证同版本归档，再核对成员、完整 SQL 切片和 Lean 输入；不把新增 JSON 自身的哈希用作来源信任根。

快照重建器还核对两级映射的全部列及所列原生多项式差，保留每条日志全部 11 列。正常重放及四项变异拒绝通过。历史状态 `CW d3:(16,145)[3]→(19,147)[1]` 虽未找到独立直接 root 日志，但已识别一组充分的原生代数依赖：更早 `D461961: CW d3:(15,137)[0]→(18,139)[0]` 乘 S0 `(1,8)[0]`，与 `D153861: S0 d3:(15,138)[0]→0` 乘 CW `(1,7)[0]` 相加。源像分别为 `[2,3]` 与 `[2]`，目标像为 `[1]` 与零，原生坐标相加得到 `[3]→[1]`。

这只是独立代数重构，数据库没有记录这些 parent 边。两条早期实际 D、两个实际乘子循环、实际模 Leibniz、CW relation13675 与球面 relation10936 的模作用/坐标比较均须落实。快照保留两个完整祖先分支，未把其失败 trial 当作已证；例如 461958 的记录页与诊断中的 d40/d999 仍分别保留，不能按统一 d3 规则强行解读。

`LinE2.NaturalityHighStemProducts` 另外闭合了三条固定球面商等式，保留全部原生生成元：

| 定理 | 原生等式 | 固定来源 |
| --- | --- | --- |
| `native_map_column0` | `x24*x189 = x7*x279` | S0 relation rowid 10210，CSV 零基序号 10209 |
| `native_h0_product_zero` | `x0*x519 = 0` | rowid 13637，CSV 序号 13636 |
| `native_ancestor_product` | `x3*x358 = x0²*x437` | rowid 10936，CSV 序号 10935 |

```sh
lake build KIP126.Checks.AdamsE2.LinNaturalityHighStemProducts
```

三条定理均经独立 Lean 编译、公理/导入审计与错配目标拒绝，公理只有标准逻辑三项。第一条供 Ceta→S0 完整矩阵的额外列化简使用；选中向量原本不需要它。后两条供上游原生代数诊断及历史输入重构使用。这三条完整原生模块关系及对应商模等式见下节；上述球面商等式本身不解决实际模作用、实际页比较或历史微分来源。

## 完整原生模块与两项固定商模等式

`LinModule.Ceta.Model` 和 `LinModule.CWNuEta.Model` 分别使用完整的原生模块生成元和关系。系数环仍是原有 `KIP126.LinE2.E2`，保留其全部 2914 个球面生成元、231848 条球面关系及原有 `t>261` 截断。模块模型是 `Fin n →₀ LinE2.E2` 对全部原生模块关系张成子模的商；原库 `t_max=200` 只记录已计算范围，没有添加模块高次为零的关系。

| 原生对象 | 完整生成元 ID | 完整关系 SQLite rowid | 原库 E2 / d2 上限 |
| --- | --- | --- | --- |
| Ceta | `0–886`，887 个 | `1–76569`，76569 条 | `t_max=200`，`d2_t_max=170` |
| CW_nu_eta | `0–843`，844 个 | `1–69263`，69263 条 | `t_max=200`，`d2_t_max=150` |

`Generated/Modules/Ceta.json` 与 `CWNuEta.json` 保留生成元全部原始字段 `id,name,repr,s,t,cell,cell_coeff`、每条关系的 `sqlite_rowid,rel,s,t`、原生次序、schema 和版本元数据。CW 的 607 个 NULL 名称以及相应 NULL cell 数据原样保留，不被替换为零。Lean 数据保留同一完整生成元族、原关系串和次数；每 512 条关系构成一个 `relationChunk`，`relations` 恰为各块顺序连接，没有添加空关系。

`Translate/generate-module-presentations.py` 复用已有 pinned 输入加载器和 RAR 认证。CW 原库按既有 LFS 规则纳入 `Raw/manifest.json` 及唯一 canonical 清单的 `lwx_machine` 条目，大小 2727936 字节，SHA256 `8007f076e6bb78f269849758db8ec347625896607dd54d31e9fc0df770aec278`。导出器将 S0、Ceta、CW 和 `ss.json` 与同一认证 `v126.3.cw49` 归档逐字节比较，并将球面全部生成元、全部关系与现有 CSV 按原顺序逐行核对。两个模块的全部 204928 个关系项均检查生成元范围、幂编码和同质次数，不通过另选系数环或缩小生成元范围验证目标。

本轮固定的两个结论均在上述完整商模中，不附加原生关系消失假设：

```text
KIP126.LinModule.NaturalityModuleProducts.native_ceta_strings:
  Ceta.monomial "195,1,12" = Ceta.monomial "67,1,107,1,0"

KIP126.LinModule.NaturalityModuleProducts.native_cw_strings:
  CWNuEta.monomial "3,1,240" =
    CWNuEta.monomial "438,1,2" + CWNuEta.monomial "0,2,418,1,2"
```

| 固定关系来源 | 完整原生关系串 | 次数 `(s,t)` |
| --- | --- | --- |
| Ceta rowid 13125 | `195,1,12;385,1,2;456,1,0` | `(15,140)` |
| Ceta rowid 13126 | `385,1,2;456,1,0;67,1,107,1,0` | `(15,140)` |
| CW_nu_eta rowid 13675 | `3,1,240;438,1,2;0,2,418,1,2` | `(16,145)` |

三个 rowid 分别对应零基行号 `13124、13125、13674`，在 512 条分块中的位置为 Ceta 第 25 块 `324、325`、CW 第 26 块 `362`。局部成员证明接到全部关系表；`Presentation.native_relation_zero` 从定义子模成员性证明原生关系在商中为零。复用既有 `NamedElementCertificates.ModuleExpressions.check_sound_evaluate` 检查所有 887/844 个模块坐标上的证书：Ceta 的两条关系各用一次，CW 的一条关系用一次。最终定理不读取实际模型、整表认证或待构造总交付。

```sh
python3 -B KIP126/LinProgram/Translate/generate-module-presentations.py --check
python3 -B KIP126/LinProgram/Translate/test-module-presentations.py
lake build +KIP126.Checks.AdamsE2.LinNaturalityModuleProducts:olean
```

数据结果：完整重生及字节一致性检查通过，15 项测试通过，覆盖漏行、行号/次序变化、NULL/空关系、越界模块/球面生成元、错误幂和次数、截断范围变化、错误 schema 及生成文件篡改。canonical 来源、派生输出和已安装脚本的 31 项一致性检查也通过。两项固定商模定理、原生行及成员性检查、传递公理/导入审计和负例检查正式构建通过（1694 jobs）；公理仅 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`、项目公理或实际模型/总交付依赖。这里认证的是完整固定数据商模中的等式。

这些等式分别服务于 CW→Ceta 完整矩阵的额外第零列约化及一个历史微分输入的原生模乘法重构。它们不证明完整原生商模与同一实际 Ceta/CW 页的比较、实际映射坐标、实际 d3、历史乘子的循环性、实际模 Leibniz、边界排除或候选完备性。特别是历史原生日志之间没有 parent-id 边，商模等式不能把独立代数重构升级为已证历史依赖；462479/462480/462481 的实际认证状态保持未完成。

## 从原生核/像商接到实际 E3 页

新增独立 Def 模块 `SpectralSequence/Computation/PageThree/Proofs.lean` 在任意环 `R`、任意内部谱序列 `E` 和全部次数上证明五项结论：每个 E3 元素有 E2 共同代表；当 `E.r₀≤2` 时，E2 标签到达 E3 等价于实际 d2 为零，`IsBoundaryBy E 2` 等价于实际 d2 像中的成员性；标签代表同一个 E3 元素、以及两个已代表的 E3 元素相等，都由标签之差在完整 d2 像中刻画。证明直接使用规范商页和 `Z_succ/B_succ`，没有另行假设 E3 是核/像商。

`LinProgram.BranchPageThree.representatives` 将已闭合的四个原生代表运输到任意 `ModuleCat ℤ` 谱序列，量化**每个**实际 E3 元素。其显式输入是起始页界、三个完整 ℤ 线性坐标同构（5、4、4 维）和两个对全部向量成立的实际 d2 交换等式；没有加入 `CandidateCoverage`、非零性、整表结果或源延拓假设。

```sh
lake build KIP126.Checks.SpectralSequence.PageThree \
  KIP126.Checks.AdamsE2.LinBranchPageThree
```

四个新模块均独立 Lean 编译通过且无警告，公理审计只有标准逻辑公理。这一通用条件运输定理已闭合；其实际 CW 应用仍需同一模型中的 CW 对象、d2 次数 `(2,1)`、三份完整坐标同构及两交换方块。此外，源 `(15,144)[1]` 的 E3 延拓也必须证明，不能由目标空间覆盖或 D 标签推断。因此尚未构造实际 CW 的 `CandidateCoverage`。

## 462481 的同模型条件自然性重放

`Interface.Solution.LinProgram.NaturalityHighStem.row462481` 现已给出精确原生输出 `d3:(15,138)[2]→(18,140)[2]`。它重用同一 Ceta、eta 映射、实际 topCell、两份 tower comparison 和传入的同一个 presentation `P`。新增通用 `Naturality.topCell_hasDifferential_desuspendTwice` 保留全部整数页与次数；旧 245131 两个公开入口的完整类型逐字不变，证明改为共用此传输。

球面源类 `x0²*x418` 和目标类 `x0²*x437` 的归档行、同质次数及 `[2]` 坐标都已闭合，分别对应原始基底 id3002、id3140。原生日志 462480/462481 全部 11 列由重建器核对；来源 462480 保持 **N**，没有被改写为 D。

准确剩余前提是实际 `HasDifferential cetaSequence 3 (15,140) (18,142) (coordinates 15 140 1) (coordinates 18 142 0)`，以及 topCell 像经过两次降悬时源、目标的四条坐标比较。Ceta 原生坐标与实际模型的识别同样尚需构造。实际模型本身的既有基础待证命题保留，Main 的 462481 消费者因此尚未迁移。

```sh
lake build KIP126.Checks.ClassicalAdams.LinNaturalityHighStem \
  KIP126.Checks.ClassicalAdams.LinNaturalityReplay
```

五个修改/新增 Lean 模块及新旧检查均独立编译通过。坐标和 `HasCoordinates` 证明只有标准逻辑公理；条件实际重放继承已有固定模型 `sorryAx`。证明值检查确认新旧包装均使用同一共用传输，均不读取整表认证或待构造总交付。它们不把非空坐标升级为后来页上的非零结论。

## 已闭合的悬移与重编号规则

`Suspension.TowerComparison.desuspend_adamsI`、`desuspend_adamsJ`、`desuspend_adamsK` 已从既有 tower/layer 方块证明：前两项交换，K 带负号。所有整数次数及 tower stages 保留，没有加入新的 differential-compatibility 假设。实际有限循环与边界的保持也已经证明；循环见证的负号来自同一个 K 方块。

`SSDataMorphism.representsOnPage_reindexed` 和 `hasDifferential_reindexed` 保持规范商页映射，并支持任意次数重排；微分传输要求重排与微分次数平移相容及真实交换方块。它们不要求重排为加法同态。旧 ordinary 自然性接口的完整类型保持，并从新通用规则推出。

I/J/K、这两条重编号规则以及 `desuspendPage_differential` 均通过独立编译和传递公理审计，只依赖标准逻辑公理。后者对所有自然页 `r ≥ 1` 给出真实商页微分的单次降悬反交换公式，保留目标次数转换。有限及无限循环、边界的保持也已闭合。内部真实 SSDataMorphism、规范页映射比较、单次内部反交换律和两次降悬合成现均已闭合。`desuspendTwiceInternalPage_d` 与 `hasDifferential_desuspendTwice` 的传递公理同样只有标准逻辑公理，`row245131` 已删除额外通用兼容性参数。

```sh
lake build KIP126.Checks.ClassicalAdams.LinSuspensionReplay
```

## 种子 5487 输入中的三条闭合代数等式

复用现有提取审计 `docs/audits/issue152/seed5487-next.json`，从同一 96 生成元闭包选取实际标识 `0,524288,524289,1048577,1572866,2097152,3145729`。完整闭包语义 SHA256 为 `088958541d91f6a987c825ab94a3266001cf94e6eccdf19757ac9b39d92c69fa`。原数据库的 `d、f` 字段与提取器计算的辅助见证 `d_f、f_d、associator` 明确区分；辅助见证可以被证书验证，其存在不等于原生算法正确性证明。

`KIP126.Computation.Secondary.Seed5487.row1048577_d_squared` 证明实际行 `(s,v,t)=(2,1,4)` 的全部两条路径相消。`row1572866_d_f` 证明行 `(3,2,10)` 的原生 `f` 经原生第一微分后，恰等于辅助见证中的三项表达式。`row3145729_d_f` 进一步证明行 `(6,1,16)` 的原生 f 经行 2097152 的原生 d 后，等于辅助 d_f 的两项表达式；该行直接出现在种子两个端点 4194320/4194319 的原生 f 中。这三条函数等式覆盖所有目标生成元和所有原始八坐标 Milnor 单项式，不限制次数。缺失中间像返回 `none`，不能被当成零列。当前七行选定语义 SHA256 为 `ee919f10abe5f5beeb3213b6529e598198c217555aeccfb415d838e13a2218c8`；完整96行摘要不变。

乘法语义是已有显式 Milnor 余乘法的对偶；直接复用远程导入的 `checkAll_sound` 与 `stable_product`。五个小秩乘法证书通过次数支撑定理覆盖窗口外系数，再扩到原始秩八；新增乘法采用 rank3/window12，结果为 Milnor 指数 `(2,1,1)` 与 `(5,0,1)`，没有将结论限制在窗口内。Lean 编译及公理审计通过，依赖仅标准逻辑三项；删除非零路径、缺少中间像、篡改输出的三项负例均通过。

这些结果未证明整个 96 行闭包的全部等式、associator 公式、分解正合性/极小性或到同一实际球面 `d₂` 的比较。日志 5487 的实际微分仍未认证。

从固定原程序重建并重放（数据库带时间戳，重建校验完整语义而非要求重建数据库字节相同）：

```sh
replay_dir=$(mktemp -d /tmp/kip126-secondary.XXXXXX)
python3 - "$replay_dir" <<'PY_REPLAY'
import hashlib, sys, zipfile
from pathlib import Path
archive = Path("Source/LWXMachine/source-code.zip")
if hashlib.sha256(archive.read_bytes()).hexdigest() != "dd784541626f4d693c35f3ca84d4a67e83758ac463aabe58ab6c9cc92be22a15":
    raise SystemExit("wrong source archive")
zipfile.ZipFile(archive).extractall(sys.argv[1])
PY_REPLAY
cmake -S "$replay_dir/SSeqCpp-master" -B "$replay_dir/build" -DCMAKE_BUILD_TYPE=Release -DFMT_TEST=OFF -DBUILD_TESTING=OFF
cmake --build "$replay_dir/build" --target Adams -j 4
mkdir "$replay_dir/run"
(cd "$replay_dir/run" && "$replay_dir/build/bin/Adams" res S0 45 && "$replay_dir/build/bin/Adams" d2 S0 45)
python3 KIP126/LinProgram/Translate/extract-secondary-witness.py --resolution "$replay_dir/run/S0_Adams_res.db" --secondary "$replay_dir/run/S0_Adams_d2.db" --output "$replay_dir/witness.json"
python3 KIP126/LinProgram/Translate/generate-secondary-seed5487.py --check --witness "$replay_dir/witness.json"
lake build +KIP126.Checks.ClassicalAdams.LinSecondary5487:olean
```

已使用固定原程序在新目录实际重跑，完整 96 行语义及种子端点相同。单独运行生成器 `--check` 只核查固定选定内容；核验完整闭包必须传入 `--witness`。现有提取审计是重建记录；唯一 canonical 来源清单仍是 `docs/external-inputs.json`。生成器还直接核对该清单中的原程序实体、MD5/SHA、重建记录链接、选定fixture及生成Lean输入摘要；四类来源错配均在无写入测试中被拒绝，`python -O` 重放同样通过。

## 实际单侧长层乘积的零微分规则

`adamsSphereLongLayerStageTriangleIso_connecting_eq_zero` 和 `adamsSphereLongLayerStagePairingIso_connecting_eq_zero` 证明真实 `Q_s^r ⊗ T_t → Q_{s+t}^r` 配对保持第一个输入的零连接同态条件。`adamsDifferential_longLayerStagePairing_eq_zero` 随后给出该实际页代表元的零 `d_r`，保留全部 `r ≥ 1、s、t、n、m`。公理及导入边界审计通过，只有标准逻辑公理。与 secondary 证书的第三批联合正式构建通过（1749 jobs），三个新Blueprint节点的13项声明链接核验及 web 渲染通过。

```sh
lake build KIP126.Checks.ClassicalAdams.LinReplayStagePairing
```

双侧配对仍缺实际 `y : Q_s^r ⊗ Q_t^r → T_{s+t+r}[1]`，使其沿塔映射的悬移投影等于指定的 `adamsSphereLongLayerProductBoundary`；准确条件为 `adamsSphereLongLayerProduct_exists_iff_boundaryLift` 的右侧。现有每个长度的三角补全由独立选择构造，跨长度投影相容不能自动推出。即使这一点解决，实际 `BoundaryCompatible` 和两项 `RelativeBoundaryFormula` 仍需分别证明。因此单侧规则尚不完成 152097 的 E4 Leibniz 诊断。

## 5541 的文献生产端与消费者迁移

固定原生日志为 `(5541, depth=0, reason="d2", name="S0", stem=63, s=1, t=64, r=2, x="0", dx="0", info=NULL)`。源归档基底行 401 是 `(1,64)[0]="69,1"`，目标行 416 是 `(3,65)[0]="0,1,18,2"`。

`LinE2.OneLineH6.source_eq_zero_or` 和 `target_eq_zero_or` 在完整 2914 生成元商中证明两个**完整同质分量**分别只有零与指定原生类两种可能；不是把 CSV 列表直接假定为基底。证明使用完整生成元次数数组、单项式次数穷尽及 F2 系数，传递公理只有标准逻辑公理。

`Interface.Solution.LinProgram.row5541_hasNonzeroDifferential literature P` 在同一固定球面上实例化已有 `literature.results.adamsOneLine_d2` 的 `j=6`，保留非零微分结论。源是标准 `h6`，目标是标准 `h0*h5²`；利用两分量穷尽、`P.comparison` 的满射性及这两个标准类的非零性，证明精确原生坐标与实际标准类相等。这一步不假定 presentation 的任意乘法已经等于规范 cobar 乘法。

`row5541` 给出原生日志完整的 `DifferentialStatement P ⟨5541,"d2",1,64,2,[0],[0]⟩`；`row5541_rejects_zero` 排除把目标改为零向量。两条 Main 消费者 `Computation.LinProofs.row5541` 与 `Selected.d2_h6` 保持原有完整类型，改用同一直接 witness 投影得到的 `StageInput.literature` 和 `StageInput.computation.bindings.presentation`。一般整表定理及其全部量词保留；另外五条选定行仍使用原有整表交付。

这一路径明确依赖已有 one-line 文献输入，未重放 Lin 的 secondary 算法。实际模型的已有 `sorryAx` 仍在，因此只标为条件实际结果；数据坐标证书本身已闭合。生产端不导入 Main 或待构造总交付。消费者审计沿证明值检查常量和内联结构投影，禁止读取 `ComputationInterface.results`、`ComputationResults` 及整表认证。 原布局检查按路径禁止全部 LinProgram producer 复用；为这次具体迁移，只开放 `Interface.Solution.LinProgram.AdamsOneLine.H6` 一个完全参数化模块，其余 producer 与总交付仍禁止导入，逆向 Main 依赖禁令保留。这样实际模型证书继续由 Interface 持有，Main 以同一 witness 的显式输入复用；不把实现挪入 Challenge/Def 或复制证明。18 项布局检查通过，编译后的证明值/投影审计负责进一步约束这一精确例外。

```sh
python3 KIP126/LinProgram/Translate/import-selected.py --check
python3 scripts/test-import-lin-selected.py
lake build KIP126.Checks.ClassicalAdams.LinH6OneLineProducer \
  KIP126.Checks.ClassicalAdams.LinProofs \
  KIP126.Checks.ClassicalAdams.LinSelected
```

当前检查：确定性重生成一致；7 项生成器测试通过，其中原生目标、次数、reason、页码错配均不能复用该 producer。数据证书、生产端及生产端公理/导入审计正式构建通过；包含 Main 消费者的完整根库构建也已通过（4209 jobs），消费者的证明值与内联投影审计通过。既有固定模型的 sorryAx 和直接 witness 依赖如实保留。

## 实际 CW 对象及 shift-four 映射的精确缺口

本地固定文献 `Source/LWXMachine/source/ms.tex:187–190` 用两个三角定义 `CW_a_b`；对 `CW_nu_eta`，胞次数是 0、4、6，三角为 `Cν → X → S⁶` 与 `S⁰ → X → Σ⁴Cη`。同文第221行明确允许同名的不同同伦型选择。因此必须把原生数据比较到一个在同一实际模型中明确构造的选择，数据库中的名字不能唯一指定该对象。

现有 `standardRouteModel.auxiliary` 已有实际 η、ν；同一 literature 的 `ClassicalSourceBinding` 可以绑定这些映射，但现有结果没有给出所需的 `ν ∘ (Σ³η) = 0`。原生配置中空的 ην/νη 乘积记录不提供这个实际复合为零的证明。

一条可复用的构造路线是在同一个 η-cofiber 上，由上述复合零和 `Triangle.yoneda_exact₂` 取得 `g : Σ³Cη → S⁰`，使其沿 `Σ³` 底胞限制为同一 ν。随后令 `X := cofib g`，以 `cofibδ g` 后接规范悬移合成同构作为 `X → Σ⁴Cη`。这一构造及另一条 `Cν → X → S⁶` 三角现已由同一个八面体在通用层证明，见下文；实际模型中的零复合及原生比较仍待证。悬移三角的三条箭头在奇数次悬移时均带符号，必须显式处理，不能把 shift-distinguished 当成箭头逐项不变。

`StableHomotopy.CofiberExtension.exists_extension_of_shift_comp_zero` 已从实际移位三角的 `Triangle.yoneda_exact₂` 证明任意整数移位的延拓存在；`exists_eta_nu_extension` 是同一 η/ν 的三次移位特化。两条定理保留全部对象及量词，显式假设复合为零。现统一通过 `shiftedCofiberTriangle_distinguished` 规范化三角：同构的三个分量为 `1,(-1)^n,1`，前两条箭头变为正号，连接映射保留真实符号。原两条公开定理的完整类型不变，没有新增符号兼容性输入。

```sh
lake build KIP126.Checks.StableHomotopy.CofiberExtension
```

独立编译及正式根库构建、公理/导入审计均通过，只有标准逻辑三项。`cofiber_triangle_of_extension` 保留任意整数移位、全部对象及任意满足限制等式的延拓，构造同一八面体的 `m,j`、旋转后三角与全部四个交换方块。`exists_eta_nu_cofiber_triangles` 从明确的 `η[3] ≫ ν = 0` 同时给出一组 `g,m,j`、两个规范次数的三角以及四方块：`S⁰ → C(g) → Σ⁴Cη` 和 `Cν → C(g) → S⁶`。`q` 是 `cofibδ g` 后接已定义的 `shiftFourIso`；`Cν → C(g)` 始终使用同一个八面体的 `j`，没有无证明替换为另选的 `cofibMap`。

这个里程碑服务于固定原生日志 462479 的 CW 源对象，以及 462480 所用 `CW_nu_eta__Ceta` 的 shift-four 映射。它只解决条件构造与三角比较，未给出这两条实际微分或原生模块的识别。同一固定 foundation 的八面体实例已有 `Foundation.TensorInput.triangulated`，可从 `Def.StageInput.witness.tensorInput` 取得，独立核验通过；无需增加 Challenge2 字段或换一个 foundation。该实例仍继承原基础未完成证明。

新构造已独立 Lean 核验，只依赖标准逻辑三项；正式公理/导入检查通过（1561 jobs），根库构建通过（4886 jobs）。Blueprint web、完整声明检查、活动依赖解析、18项布局检查及来源/接口静态审计均通过。两条旧延拓定理的完整类型与上一提交逐字一致，新增量词与符号也经独立复核。准确剩余内容是实际复合零、固定原生模块与选定 `C(g)` 的比较，以及上述实际商映射在所用坐标上的等式。现 route 的 `ClassicalObject` 悬移比较覆盖 sphere/Cν/detector 及其 shifts。下述新构造已从同一 foundation 取得 Cη 及任意整数悬移的实际 `TowerComparison`；CW→Cη 的四次降悬组合已在下文闭合；实际复合零、原生坐标比较和来源微分仍须落实。没有新增源假设、Challenge2 字段或替代模型来掩盖这些义务。

## 从同一 foundation 构造 Cη 悬移比较

`Suspension.Construction.towerComparison H X` 现对任意对象 X 构造现有 `TowerComparison` 的所有字段。输入只有既有稳定范畴、选定 cofiber、`tensorLeft H.HF2` 的悬移结构及同一实际单位自然变换的悬移相容性；不要求额外的塔交换律、页等价或张量正合性。

单步 `fiberIso_hom_ι` 由同一单位方块和旋转三角补全证明正号的 fiber inclusion 方块；`towerIso_mapAt` 覆盖全部整数 `s ≤ t`，包括原有常值负层。层比较从规范悬移的 cofiber 三角构造，`cofiberIso_connecting` 保留准确负号及 `shiftFunctorComm C 1 1`。零层严格取恒等同构。数据构造、交换律证明与最后的完整比较装配分别存放，未改现有 `TowerComparison` 类型。

`Interface.Solution.LinProgram.Naturality.cetaTowerComparison` 以及 `cetaShiftTowerComparison n` 已在原有实际 Cη 上实例化，其中 n 是任意整数。二者同时从同一个 `Def.StageInput.witness.tensorInput` 取得 tensor 和 unit 的实例。原 route 的两份 sphere 比较保留；六个原自然性公开定理的完整类型逐字不变，没有新增 Challenge2 字段或另选模型。

这个里程碑服务于固定日志 462479→462480 的 `CW_nu_eta__Ceta`（shift four），以及其后 462481 的 Cη→sphere 自然性链。它解决塔比较的构造，尚未证明不同三角补全选择的独立性、实际 ην 复合为零、CW/Cη 原生模块的比较或实际来源微分。下文已构造四次降悬组合；全部原生坐标等式仍待证明，不能据此标记 462480/462481 为实际认证。

```sh
lake build KIP126.Checks.ClassicalAdams.SuspensionConstruction \
  KIP126.Checks.ClassicalAdams.LinNaturalityHighStem \
  KIP126.Checks.ClassicalAdams.LinNaturalityReplay
```

通用构造及其全整数、符号和导入审计已独立核验，公理仅标准逻辑三项。含固定 Cη 实例的正式构建通过（3498 jobs）；固定实例继承原有基础 `sorryAx`，未扩大基础公理集合。固定 Blueprint 节点继续为 `notready`；通用条件构造为 `leanok`。根库和新旧自然性检查通过（4891 jobs）；Blueprint web、完整声明链接、活动标签/依赖解析、18 项边界布局检查及来源/接口静态和 Lean 检查均通过。独立复核确认负号、全整数范围及同一单位结构没有改变；六个原自然性定理的公开类型与上一提交逐字一致。

## CW→Cη→sphere 的同模型条件重放

`NaturalityCW.extension hzero` 从已证明的 η/ν cofiber 延拓与同一八面体定理只选择一次 g，定义 `CW hzero := cofib g`。`q hzero` 是这个 g 的实际连接映射后接 `shiftFourIso Ceta`，目标为原有 `Ceta[4]`。`fixed_triangles` 对同一个 g、CW 和 q 给出两条三角及同一 m,j 的四个交换方块。该接口的显式数学前提是同一实际映射的 `η[3] ≫ ν = 0`；下节新增推导在同一 presentation、literature 和公开分离性依赖下提供它，尚非无条件实际认证。`IsTriangulated` 来自原有同一 `StageInput.witness.tensorInput`，没有新增 Challenge2 字段或选择第二模型。

`Suspension.Fourfold.desuspendFourInternalPage_hasDifferential` 对任意对象、全部整数页和次数，将两次既有双降悬组合；其结论是完整 `HasDifferential` 关系的运输。`quadShiftIso` 明确把四个逐次 [1] 悬移与 [4] 比较。`hasDifferential_desuspendFour` 还提供八条代表元关系的入口。通用声明的公理仅逻辑三项。

固定原生链保持全部字段与次数：

| 原生记录 | 谱 | 精确 d₃ 原生等式 | 下一步悬移 |
| --- | --- | --- | --- |
| D462479 | CW_nu_eta | `(15,144)[1] → (18,146)[0]` | 4 |
| N462480 | Ceta | `(15,140)[1] → (18,142)[0]` | 2 |
| N462481 | S0 | `(15,138)[2] → (18,140)[2]` | — |

其中 `[0]` 是基底序号零，不是零向量。462479 的 info 保留 SQL NULL；CW 原始 ss.json 映射没有 type 字段，未把它伪造为 `top_cell`。新增 `source462479Full` 与其余两行一起，由通过摘要认证的原始 proofs.db 核对全部 11 字段。重建 trace 快照字节及 SHA256 `9ae1c39d56e62f0a48bc919ad80e4e034ae2acedcb050fd85a42189a4281c4a4` 均不变。

`NaturalityCW.cwToCetaE2` 使用同一 q 后接 `quadShiftIso.inv` 所诱导的实际 E₂ 映射，再接四次实际商页降悬。`cwToCetaE2_hasDifferential` 保留任意整数页、两个次数及所有类。`row462480` 从实际 CW 来源等式及这张**已定义实际复合映射**在两端的坐标等式，得到现有 `NaturalityHighStem.SourceEquation`。这些两端等式没有被证明或自动判定，也没有暗中假定八个中间代表元关系。

`row462481_from_cw` 将这个结果接入已有 462481 重放，使用同一 Cη、同一 presentation P 及原有 sphere tower choices，得到原始 `DifferentialStatement P output462481`。完整剩余义务是实际复合零、实际 CW d₃ 来源、两个 CW→Cη 端点比较、原有四个 Cη→sphere 降悬比较，以及 CW/Cη 坐标族与完整原生模块的识别。固定基础仍继承 `sorryAx`。三个 D/T 分支反驳及实际 E3 覆盖尚未接入，原生 D/N 标签不提供这些证明。因此这条链仍为条件重放，未标为实际认证。

```sh
python3 -B KIP126/LinProgram/Translate/extract-row462481-trace.py --check
python3 -B KIP126/LinProgram/Translate/test-native-contract.py
lake build KIP126.Checks.ClassicalAdams.LinFourfoldSuspension \
  KIP126.Checks.ClassicalAdams.LinNaturalityCW \
  KIP126.Checks.ClassicalAdams.LinNaturalityHighStem
```

四降悬与固定 CW 模型的正式构建通过（3498 jobs）；完整条件重放模块正式构建通过（3501 jobs）。原生合同全部16项测试与固定trace重建通过，包含 reason、NULL、坐标和次数的四类篡改拒绝。独立数学审阅确认全部量词、符号、同一对象选择及两端比较的作用；未新增公理、源交付或总认证读取。根库及新旧自然性审计正式构建通过（4895 jobs），Blueprint web、完整声明链接、活动依赖解析、18项布局检查、来源/接口静态和 Lean 核验均通过。编译后依赖审计同时检查私有辅助函数与内联投影；临时负例中经私有函数读取计算 results 的路径被准确拒绝。原有高 stem 重放模块内容保持不变。

## 同一 presentation 与 literature 推导 CW 的零复合

`LinE2.StemFour.component_subsingleton (s : ℕ) (hs : s < 4)` 证明完整原生 `E2At s (s+4)` 为零。它穷尽全部 2914 个生成元，次数不超过 7 时只可能使用原生 IDs 0、1、2；两个次数方程将全部单项式限定为 `x0^(s−2)*x1*x2`（且 `2≤s`）。原关系串 `1,1,2,1` 使其为零。证明针对定义齐次部分的所有单项式之张成空间，不使用 CSV 基底完备性，也不靠原有 `t>261` 截断推零。

通用 `TowerDetection.filtration_raise_of_pageTwo_subsingleton` 从实际完整 E₂ 分量消失推出 `Fˢ⊆Fˢ⁺¹`。它复用真实商页的提升判据，在 stage −1 与 stage 0 的常值段合流，覆盖初始 `s=0`。`mem_all_filtrations_of_pageTwo_zero` 对任意整数 stem n 使用**全部**自然滤过；`homotopy_eq_zero_of_pageTwo_zero_of_separated` 再以该度的显式分离性推出所有同伦元素为零，没有额外假设 E∞ 与 associated graded 的比较。上述数据与通用定理均已闭合，公理仅标准逻辑三项。

`Interface.Solution.LinProgram.EtaNu.pageTwo_stemFour_subsingleton` 取同一 bindings、依赖于它的 literature results 和同一个 `P`。低四个滤过由 `P.comparison` 搬运完整零分量（只需 `t≤7`）；所有 `s≥4` 由现有 `results.sphereVanishing` 的无界命题覆盖。`homotopy_four_zero` 显式调用现有 `Def.standardSphereSeparated 4`；`eta_nu_zero` 用标准 shift-add 同构，将同一实际 η、ν 的复合识别为四维茎元素并证明其为零，无需额外的乘法或检测比较。

**这一固定模型推导仍不是实际闭合认证。** `P` 的数学比较、同一 literature 的无界消失线、固定基础及公开未完成的 `standardSphereSeparated` 都保留。尤其分离性是本条新入口使用的明确证明债；即使它与旧固定基础的传递公理集合都显示 `sorryAx`，也不能据此声称没有新增依赖。

`NaturalityCW.row462481_from_literature` 将上述零复合用于既有 `CW hzero` 和既有重放，不选择第二个 CW，不读取待构造的总交付。原 `row462481_from_cw` 的完整声明保持不变。新入口仍要求同一个 CW 的实际 D462479、两个 CW→Cη 端点比较和四个 Cη→球面降悬比较，输出仍是固定 N462481：`d3:(15,138)[2]→(18,140)[2]`。模块／实际页识别、实际分支反驳和来源微分继续待证。

```sh
lake build KIP126.Checks.AdamsE2.LinStemFour \
  KIP126.Checks.ClassicalAdams.TowerVanishing \
  KIP126.Checks.ClassicalAdams.LinEtaNu \
  KIP126.Checks.ClassicalAdams.LinNaturalityCW
```

本里程碑正式根库及新旧自然性审计构建通过（4914 jobs），新证明模块无新增警告。数据和通用定理的传递公理仅标准逻辑三项；固定模型审计对编译后的证明值、私有辅助声明和内联字段投影检查，强制保留 `P.comparison`、同一 `LiteratureResults.sphereVanishing` 和具名的 `standardSphereSeparated` 依赖，禁止三个新模块引入直接 `sorry`/项目公理或读取计算总交付。分离性与实际零复合的 `sorryAx` 单独输出，不作为已完成认证。原两个重放入口的完整声明和证明与上一提交逐字相同。Blueprint web、完整声明链接、活动依赖解析、15 项 Blueprint 检查、18 项布局检查及来源/接口静态与 Lean 检查均通过；原生输入、trace、合同及认证状态未改。

## 长层阶段乘积与指定系数乘积的比较

`LongLayerStageComparison.defect_factors` 对所有 `r≥1`、自然阶段 `s,t`，证明已有长层—塔阶段配对投影与指定系数乘积之差，经实际张量长三角的连接映射因子化。其两端严格使用既有 `adamsSphereLongLayerStagePairingIso`、`adamsLongLayerProjection` 和 `adamsSphereLayerProduct`；`stageProjected_eq_actual` 检查 `t+(s+r)` 与 `(t+s)+r` 的真实 transport，没有另选三角补全。

`actual_eq_on_representatives` 对任意来源对象 A、B 和代表 a、b，若 a 的长连接复合为零，则两种乘积在这些代表上严格相等。证明由已有两个 inclusion 方块得到相同限制，再用同一个实际张量三角的反变正合性因子化差映射。所有正长 r、自然 s,t 和来源对象量词保留。

```sh
lake build KIP126.Checks.ClassicalAdams.LongLayerStageComparison
```

数据、证明和检查模块均已独立核验，正式检查通过；公理仅标准逻辑三项，无 LinProgram、Interface、Main 或固定 StageInput 依赖。这个比较服务于 152097 的实际乘法接入，但目前未识别该日志代表满足上述条件：零长连接复合强于一般 E_r-cycle。完整双长层配对的边界 lift y、全部 `BoundaryCompatible`、相对两项边界公式和 Lin 乘积比较仍未闭合，不能由本定理宣布 E4 Leibniz 已完成。

本轮完成后，根库及新旧自然性、商模和消费者审计构建通过（4913 jobs）；Blueprint web、完整声明链接及活动依赖解析通过。来源清单为 26 sources / 118 artifacts，22 项来源测试、51 项外部输入测试、18 项布局测试、15 项 Blueprint 测试均通过；来源/接口声明的 Lean 核验也通过。完整模块重生及15项模块输入测试通过，原生合同16项与 pinned 输入7项测试通过。原生合同快照只新增已检查 CW 数据库名，原生目标、前提和认证状态未改变；462481 trace 字节及摘要保持不变。原固定模型的基础待证命题继续公开保留，本轮闭合证书和新通用比较不引入这些依赖。

## 全页边界作用与完整商模块映射的通用定理

`BoundaryTowerAction.boundary_mul_kerK` 对任意 `r≥1`、自然滤过 s/t 和任意整数内次数 u/v，证明指定系数乘积满足 `P(B_r,ker K) ⊆ B_r`。实际长正合列给出 ker K 输入的塔代表，真实第一输入复合过渡方块保持被杀条件，再由同一系数乘积的单位限制识别边界。`tower_boundary_kernel_left` 处理全部负下界 `s−r+1<0`，没有增加 `r≤s+1` 的限制。

`boundary_mul_sameK` 进一步证明：固定真实边界 x，若 `K(y)=K(y′)`，则 `P(x,y)−P(x,y′)∈B_r`。因此对这个边界输入，乘积模边界只依赖另一输入的连接像。`boundary_mul_longLayer_zeroK` 由真实长层连接方块得到相应特化。

这些定理保留完整页范围，但**不完成原来的全循环边界相容性**：一般 r-cycle 只满足 `K(y)∈im I_(t+1,t+r)`，不必满足 K(y)=0。特别是 H6 左 cross 仍要求所有 `a:π₆₂T₃`（`I_(2,3)a=0`）和所有 `b:π₆₃Q₁²` 都满足 `P(Ja,πb)∈B₂^(4,129)`，右 cross 也仍待证。不能把 h6 的任意代表改为零长连接像，因为这会与同一文献给出的非零 d2 相冲突。原 `BoundaryCompatible`/`CrossBoundaryCompatible` 声明和状态不改。

`LinModule.Presentation.desc` 和 `existsUnique_desc` 复用标准 `Finsupp.linearCombination`、原 `evaluatePowers`、完整定义关系子模及 `Submodule.liftQ`。对任意 n、所有完整 relations、任意 E2 模块 M，若每条关系在指定的全部生成元像下为零，则构造唯一的 `Model n relations →ₗ[E2] M`，并证明每个生成元、任意原生词和关系的计算律。检查实例保留整个 Ceta→原 E2 与整个 CW→Ceta 类型，没有选择小型替代商或改变系数环。

该下降定理不替代完整原生映射的关系证书。两图全部原生像已独立固定（见下节）；75,347 条 Ceta 及 67,929 条 CW 非形式零关系的多项式约化见证已有 Python 重放结果，但尚未全部由 Lean 核验，不能据此构造已认证 map 或升级实际自然性状态。

```sh
lake build KIP126.Checks.ClassicalAdams.BoundaryTowerAction \
  KIP126.Checks.AdamsE2.LinModuleMaps
```

`BoundaryConnectingAction.projectedLongK_range` 再由实际长、短三角的正合性证明精确等式 `range(K∘π_r)=ker I_(t,t+1) ∩ range I_(t+1,t+r)`。`existsUnique_boundary_action` 将固定边界与任意长层输入的乘积唯一降到这个真实连接像空间，目标为 **ambient E1/B_r**，不是未经证明的实际页。H6 左 cross 因而精确剩下 `ker(I_(1,2):π₆₂T₂→π₆₂T₁) ∩ range(I_(2,3):π₆₂T₃→π₆₂T₂)` 上的作用消失，第一输入仍为所有被 I_(2,3) 杀掉的 π₆₂T₃ 类。这个作用尚未证为零，也未被增加为新的接口字段。

`Foundation.TensorInput.tensorSuspensionBraidingCompatibility` 直接由现有 `leftShift_eq` 与 Mathlib 的 shift transport 推出同一 foundation 的悬移—辫交换兼容性，消去这一个独立结构前提。它不改换左右悬移，也不增加 TensorInput 字段。`RightTensorSuspensionCompatibility` 的右参数自然性及结合子条件仍待构造；每个 tensorRight 单独具有 CommShift 不蕴含整个参数族的这两张交换图。即使有它们，系数公式中的 `BoundaryRight` 与有序 `NextRight` 之间在完整双 kernel 上的差仍待消去，不能用已证的第一输入过渡规则代替。

```sh
lake build KIP126.Checks.ClassicalAdams.BoundaryConnectingAction \
  KIP126.Checks.ClassicalAdams.TensorBraidingCompatibility
```

## 同一张量悬移结构的完整重建

`StableHomotopy.TensorShift.leftShift_eq_adjoint` 对任意有整数悬移的范畴和伴随证明：固定右伴随的同一悬移结构，若实际伴随单位与所选悬移兼容，则整个左伴随悬移结构等于标准伴随构造。`commShift_ofIso_roundtrip` 证明沿函子同构及其逆的双次运输恢复原结构。

`Foundation.TensorInput.leftShift_eq_adjoint` 与 `rightShift_eq_adjoint` 将这些等式用于同一个 foundation、同一个内部 Hom 及同一辫交换。它们保留所有对象和所有整数悬移，既不新增 TensorInput 字段，也不替换已有左右悬移选择。

这里尚未证明 `RightTensorSuspensionCompatibility`。令 `c_X(B)` 为原 `tensorRight X` 在悬移1的比较，精确剩余命题为：对所有 B/X/Y 和所有 `f : X ⟶ Y`，

```text
(B⟦1⟧ ◁ f) ≫ c_Y(B) = c_X(B) ≫ (B ◁ f)⟦1⟧'
(α_ (B⟦1⟧) X Y).hom ≫ c_(X⊗Y)(B) =
  (c_X(B) ▷ Y) ≫ c_Y(B⊗X) ≫ (α_ B X Y).hom⟦1⟧'
```

这两项仍须对原完整参数族证明；各个伴随的单位/余单位兼容性没有在此被当作参数自然性或 currying 的悬移兼容性。边界公式、完整 Leibniz 规则和固定模型实际认证状态均未升级。

```sh
lake build KIP126.Checks.ClassicalAdams.TensorBraidingCompatibility
```

本批四个新定理的正式构建与传递公理审计通过，仅含 `propext`、`Classical.choice`、`Quot.sound`。检查对同一 TensorInput 的每个对象和任意整数悬移分别实例化完整结构等式，并拒绝导入 Interface、Main、LinProgram 或固定 StageInput。联合根库构建4932 jobs、Blueprint声明链接与来源/接口Lean核验通过；右参数自然性及结合相容性仍保留上述原量词和待证状态。

## 两张完整原生模块映射图

`Generated/ModuleMaps` 固定同一 `v126.3.cw49` 的完整 Ceta→S0 图（887 行、IDs 0–886）和 CW_nu_eta→Ceta 图（844 行、IDs 0–843），滤过均为 0，悬移分别为 2、4。原始 `id,map`、完整 schema、version 与 ss.json 条目保存在 JSON；CW 的原 timestamp `1690291275` 及缺少 type 字段的事实原样保留。Lean 使用完整数组及 `Fin sourceGeneratorCount` 索引，不给缺失行设置默认零。两图 ID 0 的空字符串是已记录零；SQL NULL、未知哨兵和缺失 ID 不被当成零。后续数学解释必须保留该图语义，不能直接借用把空单项式视为单位元的关系解析器。

新固定原库 `map_AdamsSS_CW_nu_eta_to_Ceta_t200.db` 为 36864 bytes，SHA256 `3ba9ac7841d0e9287b10f8550abd7ce0746a5715bfad1c60a42edb93ba554272`。它来自同一已认证 RAR，纳入既有 `lwx_machine` 和 Git LFS。`generate-module-maps.py` 复用完整模块导出器的同归档、同球面、全关系核查，在 SQLite 解释前逐字比较两图的归档实体与 pinned 实体，并核对 canonical 来源身份。全图每项的球面指数、目标模块 ID 和悬移后次数均核验。

`--check` 从原始归档重建所有文件，逐字比较输出并核对 canonical manifest 中的派生摘要与未认证状态。`mathematical_map_certified` 与 `actual_model_comparison_certified` 都保持 false。完整图数据、公理及所有 ID 顺序检查不构成全关系消失、分次线性或实际映射比较的证明。

```sh
python3 -B KIP126/LinProgram/Translate/generate-module-maps.py --check
python3 -B KIP126/LinProgram/Translate/test-module-maps.py \
  --output-dir KIP126/LinProgram/Generated/ModuleMaps
lake build KIP126.Checks.AdamsE2.LinNativeModuleMapGraphs
```

本轮根库及边界作用、连接像、悬移兼容、完整商映射、原生图和既有自然性检查全部通过（4923 jobs）。新增闭合数学声明的公理审计仅含 `propext`、`Classical.choice`、`Quot.sound`；原固定模型自然性定理仍公开报告 `sorryAx`。完整图重生与19项测试、原生合同16项测试、pinned 输入7项测试通过。来源清单为26 sources / 119 artifacts，来源22项、外部输入51项、布局18项、Blueprint15项测试通过；外部来源声明的 Lean 检查、Blueprint web、全部声明链接检查和 diff 检查均通过。独立复核确认没有新增公理、收窄原目标或将生成图标为已认证映射。

完整关系认证的独立规模实验另已在 Lean 中核验 Ceta 原始行 `1–512` 和 `31233–31744`，共1024条，包含全见证中最长的56步归约（row31479）。这些是临时原型结果，尚未作为正式全图证书安装；其完整887个像仍须通过生产版定义绑定到上述正式原生图，再核验全部76569条关系并构造商映射。完整商映射及实际模型比较的认证状态均保持 false。

## 完整 Ceta 原生图的次数与商映射限制

`Presentation.homogeneousSpan` 和 `homogeneousPart` 在同一个完整商模块中取所有系数单项式乘全部生成元的 F₂ 张成空间，次数为整数双次数。没有增加关系、次数截断或零值约定，也没有断言这些子空间构成直和分解。`coefficientPart_nat` 证明非负次数的球面系数子空间与原 `LinE2.homogeneousPart` 严格相等，保留原 `E2At` 的底层值。

`map_mem_homogeneousSpan`、`desc_mem_homogeneousSpan` 保留所有生成元、所有整数次数和齐次部分中的所有元素。若全部生成元像有同一次数偏移，则完整线性映射保持相应子空间；商下降仍必须证明每条原始关系为零。

`NativeMapCertificates.ceta_nativeImage_mem` 已由 Lean 内核核验原图全部887个像，次数精确为原 Ceta 生成元次数加 `(0,-2)`。解释直接读取 `RawData.Maps.CetaToSphere.imageCode`；空字符串解释为零，ID0 的负目标次数保留。`Ceta.generatorRow_present` 证明完整输入行存在，次数读取不使用默认行；球面生成元的次数直接复用原2914行表。`cetaDescAt` 对任意自然数 s/t 将同一完整商的 `(s,t+2)` 齐次子空间线性映到原 `E2At s t`，唯一未供应的下降前提仍是全部76569条原关系消失，不是一个关系子集。

```sh
lake build KIP126.Checks.AdamsE2.LinModuleMapGrading
```

这些定理不提供 Ceta 的实际 Ext 比较、实际 cofiber 映射识别或源微分。CW 原生图的次数认证见下文；完整商映射及实际模型比较仍未标为已认证。

本批正式定向构建1704 jobs、根库4922 jobs均通过；新增声明及整个887项次数证书的传递公理检查仅含标准逻辑三项，无实际模型、Main、Interface或固定StageInput依赖。来源清单26 sources / 119 artifacts、来源/接口声明的Lean核验、18项布局测试、15项Blueprint测试及活动依赖解析通过；Blueprint web、全部声明链接检查和diff检查通过。固定原生输入、文献来源、已有bindings和实际认证状态均未改变。

## 完整目标中的 CW 原生关系证书

`NativeModuleCertificates.Support.evaluate_restrict` 与 `evaluate_embed` 对任意有限秩和任意单射证明有限支撑重排保持求值。限制方向显式要求输入、输出和每条证书关系的所有省略坐标均为空；`check_sound_embed_projection` 复用既有模块表达式检查器，将小支撑上的检查结果解释到原完整目标中。它没有替换商模块或改变系数环。

`CWMaxSupport.row67028_image_zero` 闭合原 CW SQLite row 67028 的原生目标：

```text
Presentation.evaluateRelation cwImages "2,1,766;79,1,196;90,1,187" = 0
```

该行原次数为 `(29,199)`。`cwImages` 直接读取完整844项官方 CW→Ceta 图，空字符串明确为零；三个实际图项、原始行 ID/次数和全部所用关系的原表成员性均由 Lean 核验。证书使用29个目标坐标、24次原 Ceta 关系和5条原球面关系，最终等式仍在原887生成元、76569关系的完整 Ceta 商中，系数仍为原2914生成元的球面商。

```sh
lake build KIP126.Checks.AdamsE2.LinCWMapSupport
```

这是单条原生关系的闭合证明，没有关系消失假设。全69263条 CW 关系、整张图的商下降及实际谱映射比较仍需各自落实；次数证明见下节，本证书不改变实际认证状态。

正式定向构建1701 jobs、包含该证书的根库构建4925 jobs均通过。17项声明的传递公理审计仅含 `propext`、`Classical.choice`、`Quot.sound`；检查同时核实证明继续调用原检查器及完整目标适配引理。来源清单26 sources / 119 artifacts、来源/接口字段的Lean核验、18项布局测试、15项Blueprint测试和活动依赖解析通过；Blueprint web、全部声明链接与diff检查通过。原文献、bindings、固定模型及认证状态保持原有含义。

## 完整 CW 原生图的次数与商映射限制

`CWNuEta.generatorRow_present` 对全部844个源生成元证明记录存在，再用 `Option.get` 读取原次数。`CWToCeta.generatorImage` 直接解释同一官方图为原完整 Ceta 商中的元素；`NativeModuleCertificates.Support.evaluate_nativeModuleTerms` 对任意秩、任意字符串证明有限项求值与原解析器一致，空图像单独解释为零。合法原生输入仍由固定输入导出检查负责。

`NativeMapCertificates.cw_degree_all` 与 `cw_nativeImage_mem` 核验官方全部844项图，次数为源次数加 `(0,-4)`。目标保持全部887个生成元、76569条原关系，系数保持原2914生成元的球面商；ID0的负目标次数 `(0,-4)` 和记录零都明确保留。`homogeneousModuleTermsCheck_sound` 对整个有限项列表证明次数检查可靠。

`cw_desc_mem` 保留任意整数次数和齐次部分中的所有元素；`cwDescAt` 对任意自然数 s/t 给出源 `(s,t+4)` 子空间到目标 `(s,t)` 子空间的 F₂ 线性限制。两者仍显式要求 **全部69263条原始源关系** 在同一完整图下为零。全关系认证与实际 Ext/谱映射比较仍待落实，没有新增截断、目标模型或实际认证。

```sh
lake build KIP126.Checks.AdamsE2.LinCWMapGrading
```

正式定向构建1709 jobs与联合根库构建4932 jobs均通过。34项声明的传递公理检查仅含标准逻辑三项，并检查完整目标有限项证书仍调用原模块检查器的可靠性定理。来源清单26 sources / 119 artifacts、来源/接口Lean核验、18项布局测试、15项Blueprint测试、700个活动节点的依赖检查、Blueprint web、全部声明链接与diff检查均通过。完整源关系消失和实际模型比较仍未标为已认证。

## 完整原生商映射的独立重放工具

`KIP126/LinProgram/Translate/module-map-certificates/` 直接从既有固定原始输入重建辅助理想组合见证并生成完整证书，不读取早期临时审计文件。Ceta 保留全部887项官方图与76569条源关系，CW 保留全部844项官方图、69263条源关系及原887生成元的完整 Ceta 目标；系数仍是原完整球面商。

```sh
python3 KIP126/LinProgram/Translate/module-map-certificates/replay-ceta.py --output-dir /tmp/kip126-native-ceta-replay --jobs 2
python3 KIP126/LinProgram/Translate/module-map-certificates/replay-cw.py --output-dir /tmp/kip126-native-cw-replay --jobs 2
python3 -B -m unittest discover -s KIP126/LinProgram/Translate/module-map-certificates -p 'test_*.py'
```

各入口支持 `--prepare-only` 和 `--check`；仅准备/比对生成数据不会运行 Lean，也不会升级认证状态。完整生成目标分别是 `KIP126.LinModule.CetaToSphere.all_relations_zero` 和 `KIP126.LinModule.CWToCeta.all_relations_zero`，随后构造原商上的 `nativeMap`、所有原生成元/单项式的作用定律及唯一性。最终导入/公理审计允许标准逻辑三项，拒绝实际模型和总交付依赖。

便携计划生成266个 Ceta 模块和434个 CW 模块；比早期267/437模块计划少的部分仅是复用仓库中逐字节一致的 Support、ModuleSupport、ModuleTerms，所有其余数学源字节与原计划一致，没有省略关系。独立见证重建、两张真实完整计划检查和75项工具回归测试均通过；本节不将这些生成检查报告为完整 Lean 证书已完成。

执行器在运行前与最终完成前，用同包生成器重新核实完整清单和全部生成源码，并核对固定 schema、每个原始关系块、最终定理及审计的完整依赖闭包。空计划、仅预检计划或部分目标不能产生完整认证标志。生成器、重建器、入口和实际调用的翻译辅助源均记录哈希；独占锁阻止运行期间重写输入。编译器、传递依赖产物与生成源码固定到核验过的隔离快照，每个成功收据须通过执行后的全输入检查；预检产物不能自动采用。

只有全部原生关系、完整商映射及最终审计实际通过，才可将 `complete_native_quotient_map_certified` 置为真。`actual_spectrum_map_comparison_certified` 始终为假，直至另行完成实际模型比较；当前两项全量 Lean 运行仍未报告完成。旧 Ceta 运行使用已固定的原计划，最终结果还须独立检查全关系定理和审计，不能仅凭旧执行器的完成标志认定。

## 完整 secondary 复合证书的通用检查器

`Secondary/Milnor/Products.lean` 的 `fastSingletonProductCheck_sound` 对任意秩、任意两个原秩单项式与有限候选输出，推出原有 `MilnorCertificates.IsMilnorProductAll`，结论保留全部原秩单项式。`degreeBasis_mem` 精确穷尽齐次次数，原次数支撑定理处理其他所有次数；没有缩小结论量词。快速二分幂通过原有 Frobenius 证明保持 tensorValue，再由原通用多项式环的系数抽取反射回原 `pairTensor`。沿用原 Milnor 定义，没有建立另一套乘法语义。

`Secondary/Expansion.lean` 的 `compositionCheck_sound` 和 `compose_of_checked_expansion` 把已认证乘积传入原 `resolvePaths/compose`，结论覆盖全部目标生成元和原秩单项式。有限支持并集上的奇偶比较证明全系数等式；缺像、缺乘积均失败，不能因后续抵消而省略依赖。`some []` 必须是显式提供且另有乘积证明的零值。

```sh
lake build KIP126.Checks.ClassicalAdams.LinSecondaryChecker
```

检查包含原生行 1048577 和 1572866 的独立重放，只调用原乘积证书而不导入原行证明；另检查非交换次序、错误秩、遗漏项、额外次数、单位、重复抵消、目标错配和缺失依赖。30项声明通过传递公理审计，只有标准逻辑三项；禁止 Def/Interface/Main 导入。正式定向构建1398 jobs通过。尚未将这套通用机制标作完整96行或实际球面 d2 认证。

共享 `HomogeneousCoproductTable` 自带整张表等于完整次数基及其快速余乘法的证明；`fastSingletonProductCheckWithTable_sound` 继续检查实际输入次数之和并推出同一全单项式结论。`Secondary/IndexedExpansion.lean` 的 `indexedCompositionCheck_sound`核对完整原路径列表，再用有排列证明的排序和相邻成对抵消比较表达式；排序算法的完成性不是可靠性的隐藏前提。

```sh
lake build KIP126.Checks.ClassicalAdams.LinSecondaryIndexed
```

索引检查覆盖遗漏/额外路径、错误乘积输入/目标、缺失ID/像、重复抵消和错误期望项；正向语义回归传入真正的原乘积证明。共享表检查另拒绝次数不匹配、秩改变和遗漏输出。整批运行仍必须实际检查全部15839项产品和96行，不能由这些回归替代。

包含共享表和索引复合的正式根库构建4947 jobs通过；两项检查模块共审计43项声明，均仅含标准逻辑三项。来源清单26 sources / 119 artifacts、来源/接口字段核验、18项布局测试、15项Blueprint测试及活动依赖检查通过；Blueprint web、全量声明链接、来源/接口字段的Lean核验与diff检查也通过。此记录不改变实际球面认证状态。

## 完整96行 secondary 的便携重放入口

`Translate/secondary-seed5487-certificates/` 现提供固定数据重建、完整 Lean 源生成与批次执行器。可重放命令、精确最终定理和状态含义见该包 README。两份既有审计使用的原始 SQLite 字节已保存到 `Raw/Secondary/Seed5487/`，以 Git LFS 存储并登记到唯一来源清单。它们是未修改原程序的既有重建输出，不是另行发表的数据库；重新运行程序可能改变时间戳字节，固定证书使用已审计快照。原 source archive、完整96行语义摘要、已有选定 Lean 输入及其范围均不变。

全计划为328模块，包含39张完整次数余乘法表、覆盖15839个原始有序乘积的271块、96行的288条原始复合与辅助奇偶等式，以及总定理和最终公理审计。真正的全量目标为 `KIP126.Computation.Secondary.Seed5487.Full.allNativeRows_composition_certified`，结论保留每个原始目标及全部八坐标单项式。这里只记录已生成并独立重建核对的完整计划，尚未将其标作全量 Lean 认证。

执行器复用已审查的原生商映射批次引擎，保留其固定依赖、实际 Lean 执行与成功收据机制；不修改正在运行的 Ceta/CW 批次。完整范围与生成器字节必须在运行前、最终完成前重新核验。只有包含全部依赖、总定理和公理审计的成功运行才能置 `full_native_96_composition_certified=true`。部分目标、缺失审计、生成失败和输入漂移均不能升级状态。`secondary_associator_certified` 与 `actual_d2_certified` 始终保持 false，直到对应数学问题另行解决。

独立规模试验已证明完整次数40表，并在同一完整乘积范围上验证共享表可降低检查成本。对全部96行的288项复合及96项辅助奇偶表达式，原始 Bool 检查也已实际通过 Lean；这仍不替代15839项乘积的证明，且这些预检产物不采用为正式批次收据。完整计划已从新保存的两个数据库重建核对，未缩减行、路径或单项式量词。

完整重放工具包42项测试通过，其中生成器7项、执行器35项；后者使用模拟编译验证调度和状态边界，不算数学证书。来源清单26 sources / 121 artifacts、22项来源清单回归、51项外部输入回归及对应来源/接口 Lean 声明核验通过。正式328模块批次已启动，当前全量原生认证与实际认证标志均仍为 false。

## 后续依赖与实际接入边界

| 目标 | 精确剩余义务 | 可复用模块 |
| --- | --- | --- |
| 152097 反驳 | 在同一实际 E4 上构造乘积，证明与两条已闭合 CSV 等式兼容，并从 trial 的微分和 multiplier 的零微分得到诊断的零源微分 | `TowerLongLayer/Pairing`、`ReplayProducts`、`TrialRefuted` |
| E4 Leibniz | 构造实际长层配对的 `ProjectionCompatible`、`BoundaryCompatible` 和 `RelativeBoundaryFormula` 实例；最后一个命题不能重新作为黑箱输入并声称已解决 | `TowerLongLayer/Pairing/Sphere/Stage` 的既有闭合三角比较及新 `Comparison`；零长连接代表的投影比较及 `B_r×ker K⊆B_r` 已证，一般循环的非零连接像作用仍待证 |
| 目标非 B3 | 对 `(9,47)` 的 `x0³*x36`，证明同一比较下 `¬ IsBoundaryBy sphereAdamsData 3 (9,47) z`；完整早期差分/边界空间及相关 d2 种子都必须证明 | `State/Proofs` 的实际商页零判据 |
| 来源到达 E4 | 对 `(4,42)[1]` 给出实际 `ReachesPage`；先前 C2h6/Ctheta5 路径的对象、映射和坐标不能由日志存在推出 | 既有实际 tower / top-cell 比较 |
| 候选覆盖 | 对准确 context/window 构造 `CandidateCoverage`，排除全部其他候选；保留 trial 数量不是覆盖证明 | 既有 `CandidateElimination.sound` / `CandidateExhaustion.sound` |
| secondary d2 种子 5487 | 已闭合选中行的 d² 与 d∘f 等式；整个96行、associator公式、分解正合/极小性与实际球面d2比较仍待证 | `Translate/extract-secondary-witness.py` 与 issue152 原有审计 |
| 245131 实际认证 | 实例化上述来源及四条坐标比较；来源原始数据已补，双降悬通用定理已闭合；仍需实际比较 | `Naturality` |
| 462481 实际认证 | Ceta 来源462480的实际微分、同一 topCell 的四条降悬坐标比较；CW→Cη→sphere 条件链已构造；复合零现可由同一P、literature及未完成的固定分离性推导；实际仍需这些依赖落实与完整原生模块比较、实际d2坐标比较、完整源到达E3及所有祖先trial反驳 | `Naturality`、完整原生矩阵证书和 `row462481-trace.json` |
| 消费者迁移 | 5541 已改用显式 one-line 文献和独立坐标证书；其实际基础仍待证，另外五条选定行尚依赖整表。只有实际已经供给的结果才接到同一 `literature`、`bindings.presentation`、`standardRouteModel`；不读取待构造的 `Interface.Solution.challenge2` 来制造 producer | 现有 `ComputationResults`/Main 消费层 |

本次没有新项目公理、Challenge2 根字段、独立 literature、替代实际模型或总交付读取。较早复用的 `row5434` 是由同一 literature 中 one-line 定理和独立坐标证书得到的条件实际结果，不等于重放原生 secondary 算法。

## 统一校验

```sh
lake build KIP126.Checks.AdamsE2.LinReplayProducts \
  KIP126.Checks.AdamsE2.LinReplayCoordinates \
  KIP126.Checks.AdamsE2.LinNaturalityCoordinates \
  KIP126.Checks.ClassicalAdams.LinSuspensionReplay \
  KIP126.Interface.Solution.LinProgram.Products.Trial152097 \
  KIP126.Checks.ClassicalAdams.LinNaturalityReplay \
  KIP126.Checks.ClassicalAdams.LinReplayRules \
  KIP126.Checks.ClassicalAdams.LinLowStemProducer \
  KIP126.Checks.ClassicalAdams.LinOneLineProducer \
  KIP126.Checks.ClassicalAdams.LinReplayStagePairing
lake build +KIP126:olean \
  KIP126.Checks.ClassicalAdams.LinH6OneLineProducer \
  KIP126.Checks.ClassicalAdams.LinProofs \
  KIP126.Checks.ClassicalAdams.LinSelected \
  KIP126.Checks.ClassicalAdams.LinNaturalityHighStem \
  KIP126.Checks.ClassicalAdams.LinNaturalityReplay \
  KIP126.Checks.AdamsE2.LinBranchD2Coordinates \
  KIP126.Checks.AdamsE2.LinBranchPageThree \
  KIP126.Checks.SpectralSequence.PageThree \
  KIP126.Checks.AdamsE2.LinNaturalityHighStemProducts \
  KIP126.Checks.ClassicalAdams.LinSecondary5487 \
  KIP126.Checks.StableHomotopy.CofiberExtension \
  KIP126.Checks.ClassicalAdams.SuspensionConstruction \
  KIP126.Checks.ClassicalAdams.LinFourfoldSuspension \
  KIP126.Checks.ClassicalAdams.LinNaturalityCW
lake build KIP126.Checks.AdamsE2.LinNaturalityModuleProducts \
  KIP126.Checks.ClassicalAdams.LongLayerStageComparison
python3 -B KIP126/LinProgram/Translate/generate-module-presentations.py --check
python3 -B KIP126/LinProgram/Translate/test-module-presentations.py
python3 scripts/check_source_inventory.py
python3 -m scripts.test_check_source_inventory
python3 -m scripts.test_external_inputs
python3 scripts/check_external_inputs.py --lean-check /tmp/linprogram-certificate-external.lean
lake env lean /tmp/linprogram-certificate-external.lean
python3 scripts/test_stage_boundary_layout.py
python3 scripts/blueprint_frontier.py --output-dir /tmp/linprogram-certificate-frontier
python3 -m scripts.test_blueprint_frontier
leanblueprint web
lake exe checkdecls blueprint/lean_decls
git diff --check
```

来源清单（26 sources/117 artifacts）、来源审计22项、外部输入51项、边界布局18项、Blueprint frontier15项和活动依赖解析已通过。原有 E2、staircase、proofs、route 重建检查通过。统一六项 Lean 构建已通过（3504 jobs）；自然性条件封装与导入/公理审计通过；来源声明/module/field 的 Lean 校验通过；Blueprint web 渲染通过（固定 0.0.20 环境，仅原有 `relax` renderer 警告）。原生合同现15项测试通过（含新增 N→N 来源与 trace 前提防擦除检查）。第二批五目标正式构建通过（3498 jobs），包括固定原生坐标、双降悬、固定坐标自然性入口和同一presentation乘法运输。来源/字段静态核验与Blueprint渲染已重放；本轮来源/字段Lean核验已通过（无输出、exit 0）。包含消费者迁移的根库构建已通过（4209 jobs）；随后全部新增证书的统一补建通过（4891 jobs），余纤维延拓及其检查的正式构建通过（4882 jobs）。完整Blueprint声明检查最初发现两个已有声明没有由根库导出，现已通过直接导入既有 `Interface.Solution.Literature.StandardSphere` 模块补齐；根库重建（4884 jobs）与 `lake exe checkdecls blueprint/lean_decls` 均通过。这个导入修复没有改动两条原声明及其前提。此前定向核验的八个Blueprint节点共46项声明，现也纳入上述完整声明检查。

本机的固定 renderer 位于 `/tmp/kip126-lean-retry-blueprint/bin`，重放时可将该目录加入 PATH 后运行 `leanblueprint web`。

## 远程研究资料复用

远程提交 `295adaedc` 的 `Lin-program/` 已原样合并，首批证书与合并提交 `2a3c5c5c7` 已同步远程。该独立研究项目没有到本仓库固定球面模型的比较证明；其有限范围认证不扩展为本次实际目标的认证。已有 `Ceta__S0` 代数块只覆盖源 `t≤12`，不覆盖本目标 `t=19,21`；S0 `(6,44)` 的导入 d2 矩阵也不是原生日志 5487 的 secondary 算法证明。

为后续有限链等式直接复用原有 Milnor 核，首批在根 Lake 注册了所需非默认模块，未复制数学主体或纳入旧项目的全部生成批次。`MilnorCertificates.StableProduct` 已正式构建，打印的乘法/秩稳定性定理只有标准逻辑公理。

本批新增的完整原生分支商、E3 条件运输、462481 条件重放、5541 消费者迁移、第三条 secondary 等式和通用余纤维延拓，均已有正式构建及 Blueprint 声明核验。独立复核确认没有缩小量词、删除剩余前提或读取待构造总交付；实际模型的未完成数学义务仍如上记录。


## Module organization and shared exhaustion (2026-10-10)

The 27 module moves and module navigation are recorded in
`KIP126/LinProgram/README.md`. Public Lean names and complete public statement
headers remain unchanged. The former OneLine source/target names are now grouped
by AdamsOneLine, Hopf, Products and Naturality; basis catalogue, certification and
fixed-model transport are separately named. Generic singleton-span and linear
comparison arguments live in `Def/Algebra/TwoElement/Proofs.lean`, and the six
original degree components and their fixed-model identifications reuse them.
No source, basis, comparison, nonzero or differential premise is weakened.
Historical trace bytes and frozen full-replay producers are unchanged.

### Validation of the organization change

The 27 migrated modules and the two square-proof modules retain all original
public statement headers. The first compiled API comparison covers 255
non-internal declarations: every mathematical type and axiom set is unchanged.
Ten generated constructor/parser auxiliaries have different hygienic bound
variable names because their owning file moved; a Lean expression comparison
ignoring only binder names verifies the rest of each type exactly. The square
API snapshot contributes eight declarations (one already in the first snapshot).
The final comparison covers 262 distinct declarations, with no missing or added
names, no mathematical type changes and no axiom-set changes. Explicit
normalization of `dataH6Sq` preserves its previously generated `dataH6Sq.eq_1`
equation lemma, whose disappearance was detected by this comparison.

The following checks have passed for this change: 140 existing Python tests
(stage boundaries 18, Blueprint frontier 15, external inputs 51, source inventory
22, augmentation 16, native contract 16, certified replay 2); source inventory
(26 sources, 121 artifacts); external-input static field/declaration checks;
Blueprint active dependency parsing and web rendering; source checks for both
square-proof modules; and compiled generated replays for native rows 5432 and
5434. The two replay proofs still report the existing fixed-model `sorryAx`.
Frozen generation input hashes, canonical input manifest and historical trace
bytes are unchanged. No new actual certification is claimed.

The complete root build and all 15 targeted Lean audits pass (4974 jobs),
including the final incrementally rebuilt square modules and root export.
The post-rebuild API comparison, external-input Lean check, complete
`lake exe checkdecls blueprint/lean_decls` run and `git diff --check` pass.
The original large Route/AlphaOne consumer recompilations account for most of
the verification time. This records interface and organization preservation;
it does not certify the still-unfinished actual-model comparison or foundation.

The current replay entry points are:

```sh
lake build +KIP126:olean
lake build KIP126.Checks.ClassicalAdams.LinOneLineProducer \
  KIP126.Checks.ClassicalAdams.LinH6OneLineProducer \
  KIP126.Checks.ClassicalAdams.LinH1Producer \
  KIP126.Checks.ClassicalAdams.LinLowStemProducer \
  KIP126.Checks.ClassicalAdams.LinNaturalityReplay \
  KIP126.Checks.ClassicalAdams.LinNaturalityHighStem \
  KIP126.Checks.ClassicalAdams.LinNaturalityCW \
  KIP126.Checks.ClassicalAdams.LinEtaNu \
  KIP126.Checks.ClassicalAdams.LinProofs \
  KIP126.Checks.ClassicalAdams.LinSelected \
  KIP126.Checks.AdamsE2.LinReplayProducts \
  KIP126.Checks.AdamsE2.LinReplayCoordinates \
  KIP126.Checks.AdamsE2.LinNaturalityCoordinates \
  KIP126.Checks.AdamsE2.LinNaturalityHighStemProducts \
  KIP126.Checks.AdamsE2.LinNaturalityModuleProducts
python3 -B KIP126/LinProgram/Translate/replay-certified.py --row 5432 --output-dir /tmp/lin-organization-row5432
lake env lean --root=/tmp /tmp/lin-organization-row5432/GeneratedReplay.lean
python3 -B KIP126/LinProgram/Translate/replay-certified.py --row 5434 --output-dir /tmp/lin-organization-row5434
lake env lean --root=/tmp /tmp/lin-organization-row5434/GeneratedReplay.lean
python3 -B scripts/test_stage_boundary_layout.py
python3 -B scripts/check_source_inventory.py
python3 -B scripts/check_external_inputs.py --lean-check /tmp/lin-organization-external.lean
lake env lean --root=/tmp /tmp/lin-organization-external.lean
python3 -B scripts/blueprint_frontier.py --output-dir /tmp/lin-organization-frontier
leanblueprint web
lake exe checkdecls blueprint/lean_decls
git diff --check
```

## 分支迁移交接（2026-10-10）

本节是迁移前的最新快照；上文“正在运行”“当前批次”等措辞保留为各里程碑的历史记录。原 P0–P7 goal 保持 **paused、未完成**，此次仅收尾保存，不启动新证明任务，也不提升任何实际认证状态。目录整理与通用证明已经保存在 `c72e63b59`；此后新增的是下面的 Blueprint 路线和迁移审计记录。

### 已保存的路线与证明边界

`blueprint/src/chapters/computation_schema.tex` 的 `sec:lin-native-presentation-construction` 新增六个 open 节点：原生代表元规格、分解正确性、统一生成元类与乘积、固定球面比较、商映射下降及双射、实际代表元乘法比较。它们通过 `\uses` 接到既有 `thm:bounded-sphere-multiplication`，并复用既有 Ext/cobar 比较及数据基底认证节点。`content.tex` 已增加导航。

这些节点全部标为 `\notready`，没有宣称新的 Lean 实现，也没有新增公理、交付字段、实际模型或读取待构造总交付。合同说明按现有 Lean 类型澄清：`P.product` 覆盖所有非负输入次数，数据比较只要求总内部次数不超过 261。`P` 的真正构造、同一实际模型的基础义务、全循环乘法/边界比较、实际来源微分与候选反驳、其余消费者迁移仍未完成。精确数学剩余项见上文“后续依赖与实际接入边界”及新增 Blueprint 节点。

### 已停止的全量证书批次

已检查三个 runner 和残留 worker 记录对应的进程，未发现仍在运行的原批次进程；无需为迁移终止任务。状态文件中的 `phase=running` 和任务列表是陈旧记录，不能据此判断任务活跃。读取的历史状态为：

| 批次 | 历史 success / 总模块数 | 观察到的收据数 | 完整原生认证 | 实际认证 |
| --- | --- | --- | --- | --- |
| Ceta → sphere，旧完整计划 | 40 / 267 | 40 | false | false |
| CW → Ceta | 165 / 434 | 165 | false | false |
| secondary seed 5487 | 213 / 328 | 213 | false | false |

这些数字是模块数，不是已认证关系数；此次没有重新核验每份旧收据的全部输入与编译产物。原始状态、清单摘要和进程核对结果保存在同目录 `migration-checkpoint.json`。Ceta 的 267 是旧计划模块数；仓库便携入口为 266 模块，差异是共用支持模块复用，不能直接混用完成计数。

历史状态、manifest、日志、收据和临时脚本已逐字核对后备份至本机持久目录：

`/inspire/hdd/global_user/czxs25250150/ops/tmp/linprogram-migration-20261010/partial-replay-evidence.tar.gz`

归档的 SHA-256、大小和成员数记录在 `migration-checkpoint.json`。这个本机备份不随 Git 迁移，不含编译产物和冻结依赖库，也不是完整认证或可直接恢复的构建快照。原 `/tmp/lin-native-ceta-full`、`/tmp/lin-native-cw-production`、`/tmp/lin-secondary-production` 均保留；如需带走部分编译缓存，应保留这些完整目录，并由 runner 重新验证，不得只复制成功标志。

### 迁移后的入口

先恢复 `docs/external-inputs.json` 登记的 Git LFS 实体（包括两个 secondary SQLite 快照）；LFS 指针不能代替数据库内容。原生完整重放可完全从仓库中的固定输入和下列入口重建，不依赖上述临时目录：

- `KIP126/LinProgram/Translate/module-map-certificates/README.md`：Ceta/CW 准备、检查及全量重放。
- `KIP126/LinProgram/Translate/secondary-seed5487-certificates/README.md`：完整 96 行 secondary 计划及重放。
- `KIP126/LinProgram/README.md`：整理后的模块位置。

换 checkout 路径后重新生成 manifest；旧收据只有在全部输入键及输出摘要重新核验一致后才可复用。保持完整原生认证和实际认证分开：即使所有批次跑完，仍需独立完成实际谱/微分比较。新证明工作应从 Blueprint 依赖节点继续，而不是从 Main 的临时总交付公理反向取值。

### 本次校验

此次没有修改 Lean 源码；`c72e63b59` 的完整构建和 262 项公开声明比较记录见上一节。新增 Blueprint 路线已通过网页构建、所有活动标签/依赖及无环性解析、来源清单检查（26 sources / 121 artifacts）、外部接口静态检查和生成的 Lean 接口核查、完整 Blueprint Lean 声明链接核查及 `git diff --check`。六个新节点均保持未完成，已有存在性目标确实依赖新增构造节点。

从 checkout 根目录复查文档与接口：

```sh
python3 -B scripts/blueprint_frontier.py --output-dir /tmp/lin-migration-frontier
python3 -B scripts/check_source_inventory.py
python3 -B scripts/check_external_inputs.py --lean-check /tmp/LinMigrationInputs.lean
lake env lean /tmp/LinMigrationInputs.lean
leanblueprint web
lake exe checkdecls blueprint/lean_decls
git diff --check
```

本次运行使用 `requirements-blueprint.txt` 指定的 leanblueprint 0.0.20。完整原生批次没有重新启动；不要求在分支迁移前完成尚未解决的数学研究。

## 迁移到 Kervaire126（2026-10-10）

目标仓库为 `https://github.com/SII-MATH/Kervaire126`，目标分支为 `codex/linprogram-certificate`。迁移前旧仓库分支端点为 `364aec38f`，旧仓库最新 main/develop 为 `9d2601af4`；新仓库 develop 的迁移基线为 `e0efff36b`。

新 develop 已包含额外基础证明、Section 7 工作及移除 KIPBase/调整 CI 的提交；旧仓库曾压缩合并历史。因此此次直接合并新 develop，保留双方历史，不向旧 develop 重放它已压缩接收的旧提交。新分支同时包含旧证书分支和新 develop 的全部祖先。旧远程分支保持 `364aec38f`，本地另保留 `codex/backup-linprogram-kip126-20261010`。当前工作分支跟踪 `kervaire126/codex/linprogram-certificate`；`origin` 继续指向旧仓库，以免改变同仓库其他工作区的默认远程。

冲突处理保留以下内容：

- `SphereClasses/Product/Proofs.lean` 同时保留等式运输、cobar 乘积公式和新 develop 的右加法/整数线性引理。
- `MilnorModule/Resolution/Raw/Proofs.lean` 复用既有对偶通用引理完成三个链等式，并保留新 develop 的全部投射性构造；`TrivialDual/Raw/Proofs.lean` 对相同公开陈述保留原已检查证明。
- 新增有限基底证书放入整理后的 `BasisCatalogue/FiniteCertificates.lean`，所有新消费者导入同步；未恢复旧目录包装或重复公开声明。
- Blueprint 保留双方不同的谱序列节点、悬移构造和原生 presentation 路线，修正已经有参数化证明的坐标单射性和系数分解比较说明。固定分解存在性、原生比较及实际认证状态保持独立。
- 保留新仓库 CI、AGENTS 和 KIPBase 移除范围；保留本分支原生证书所需的三个非默认支持库。`Lin-program`、固定原生数据和 `docs/external-inputs.json` 与迁移前完全一致。

Git LFS 对象已同步到新仓库（本次传输 13 项，约 654 MB；分支引用预检查共 14 项）。已有批次的本机归档及停止状态见上一节；此次没有重启全量原生批次，也没有改变 goal 的暂停状态。

迁移验证全部通过：完整 `lake build +KIP126:olean`（5009 jobs）；新仓库 `scripts/check.sh`（101 项边界/来源/Blueprint 测试、7 项选定行导入测试、7 项原始证明导入自测）；外部来源/接口生成检查及其 Lean 核验；Blueprint web、活动依赖图及全量 Lean 声明链接。相对新 develop 的差异检查通过（`Lin-program` 为逐字保留的既有研究导入，不做格式清理）。

额外以 `lake env lean` 逐个重放的十项现有审计为：`Checks/Steenrod/MilnorDualCobar`；`Checks/ClassicalAdams/` 下的 `LinH6OneLineProducer`、`LinNaturalityCW`、`LinNaturalityReplay`、`LinNaturalityHighStem`、`LinProofs`、`LinSelected`、`LongLayerStageComparison`；`Checks/AdamsE2/` 下的 `LinReplayProducts`、`LinReplayCoordinates`。这些均位于 `KIP126/`，保留完整公开语句与既有依赖边界。条件实际重放仍报告其固定模型的 `sorryAx`，没有因此升级为实际认证。

```sh
LEAN_NUM_THREADS=4 lake build +KIP126:olean
bash scripts/check.sh
python3 -B scripts/check_external_inputs.py --lean-check /tmp/LinKervaireMigrationInputs.lean
lake env lean /tmp/LinKervaireMigrationInputs.lean
leanblueprint web
lake exe checkdecls blueprint/lean_decls
```
