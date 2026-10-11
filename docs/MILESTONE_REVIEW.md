# Milestone 首轮数学审查包

本包供数学家与形式化负责人开会逐项作出决定；所有卡片初始状态均为 **待人工审查**。
内容来自源码与论文对读，不代表人工认可、接口已冻结或证明已经完成。
审查基线：[`1151a405a004d74513f0b788da99a275a8640adf`](https://github.com/SII-MATH/Kervaire126/tree/1151a405a004d74513f0b788da99a275a8640adf)，即 2026-10-11 更新检查的 `develop` 快照。
下面行号只定位该基线；相对链接、完整声明名与 Blueprint label 应一起保留，后续改动按版本复核。
范围遵守 [PROJECT_BOUNDARY.md](../PROJECT_BOUNDARY.md) 与 [AGENTS.md](../AGENTS.md)：终点是标准 `h₆²` 非零永久存活。
本包只提审查问题和候选接口；不新增 Lean 声明、项目 axiom、Challenge2 字段或中间 Challenge 镜像。

## 会议顺序与记录要求

建议依次审 M08-A、M08-B、M16/M19、M20，再确认 M09–M11 的通用数学签名。
每张卡必须分别记录：数学陈述是否充分、与论文是否对齐、实际依赖是否独立、允许冻结的版本。
“源码已有 proof body”“当前模块可编译”“传递依赖已闭合”是三个不同状态。
批准接口后可以让下游按它开发；该决定不使上游 `sorry`、开发 axiom 或外部输入自动消失。
本轮审查人、日期、结论与依据均留待实际审查填写，不预填姓名或通过状态。

## M08-A：从完整 staircase row 3005 到同一个 route interpretation

### 目标与现有合同

现有 `KIP126.Computation.Route.sphere_facts` 位于 [Computation/Route.lean](../KIP126/Main/Solution/Computation/Route.lean)，基线 332 行；大部分局部证明已拆入 `Computation/Route/` 子模块。
它对一般 `(I : Inputs D L G) (V : SphereVanishingLine H)` 返回 `Derived.SphereFacts I.realization`。
357 行的缺口属于 `d3_h4_x_109_12`：要证明命名 `d₃` 的靶在真实 E₃ 页非零。
已有 private `h4_d3_nonzero_of_remaining_span`（69 行）把剩余问题压缩为一个 `d₂` 列的 span 条件。
321 行的 `h4_d3_nonzero_of_remaining_column` 已证明“该列为零”足以满足它。
对应 Blueprint：[near126.tex](../blueprint/src/chapters/near126.tex) 的 `evidence:near126-core`；计算交付见 [computed_inputs.tex](../blueprint/src/chapters/computed_inputs.tex)。

### 已核实的数据与已有桥梁

| 项目 | 基线证据 | 数学意义或限制 |
| --- | --- | --- |
| 原始 row 3005 | [Shard023.lean](../KIP126/LinProgram/Generated/Staircase/Shard023.lean)，72 行，shard 23 / offset 61 | `(s,t)=(14,138)`，base=`[2]`，diff 未知，level=9000 |
| 确定性解码 | [State/Data.lean](../KIP126/LinProgram/Interpretation/State/Data.lean)，`State.decode`，53 行 | 解为 `.reaches 1000 14 138 [2]`，不是非零永久存活 |
| 完整逐行交付 | [Delivery.lean](../KIP126/Interface/Challenge/Computation/Delivery.lean)，`SphereStaircaseInterface.rows_sound` | 解码与数学真实性均须交付，lookup/hash 本身不能证明它 |
| 同一 comparison | 同文件 `ComputationResults.route_presentation` | `routeRealization.sphere ... x = presentation.comparison ... x` |
| 选定 basis 编码 | [Route/Selected.lean](../KIP126/LinProgram/Route/Selected.lean)，227 行 | `(14,138)` 的 index 2 对应 `23,1,190,1` |
| route 的坐标等式 | [Certification.lean](../KIP126/LinProgram/Interpretation/Route/Certification.lean)，`Inputs.csv` | 必须与完整 CSV `[2]` 对齐，不能只凭两个整数索引相同 |

关键区别：`ComputationResults` 已有 `sphereStaircase`、`route_presentation`；`ComputationInterface.route` 投影出的 `Inputs` 只保留 selected claims 等七类认证。
在一般 `I : Inputs D L G` 的当前类型中，没有完整 `sphereStaircase` 字段；也没有把 row 3005 作为 selected claim 交付。
这说明存在需要审查的数据可达性问题；尚未据此证明一般 `sphere_facts` 的陈述不成立。

### 候选窄接口（建议，尚未实现或 elaboration 检查）

固定同一 `input : KIP126.Challenge2`，令 `I := input.computation.route`，`E := sequence standardRouteModel .sphere`。
建议先交付以下明确命题，再应用已有 private helper：

```lean
ReachesPage E 1000 (14, 138) (I.realization.basis .sphere 14 138 2)
-- 从前一命题推出当前缺口所需的更强充分条件：
E.d 2 (14, 138) (I.realization.basis .sphere 14 138 2) = 0
```

若一般 `I` 的现有数据足够，也可只证明原来的较弱条件：

```lean
E.d 2 (14, 138) (I.realization.basis .sphere 14 138 2) ∈
  Submodule.span ℤ {I.realization.basis .sphere 16 139 1,
    I.realization.basis .sphere 16 139 2}
```

候选推导必须依次核对：row lookup → decode → `rows_sound` → `HasCoordinates` 的 CSV 唯一性 → `route_presentation` → 同一个 `I.csv` → `d₂=0`。
这里只需要从 E₁₀₀₀ 的代表元得到早页微分为零；不需要把 level 9000 解释成 E∞，也不需要新的 vanishing-line 假设。

### 可选修正与下游影响

1. **保留一般签名：** 由现有 `I` 的乘法、basis、differential 关系证明较弱 span 条件；需给出独立数学推导。
2. **使用现有完整交付：** 为固定 `input` 写普通 Main theorem，将上面的同输入事实传入局部 proof；不增加 Challenge2 字段。
3. **扩充 selected 数据：** 经审核修改确定性 selection 与认证，使 row 3005 成为实际可用 claim；需同步其生成物、来源和消费接口。
方案 2 或 3 会改变 `sphere_facts` 的组织或适用范围，必须明确版本化；不能暗中把一般 theorem 改成只对固定实例成立。
下游影响包括 Prop7.8、α₁/弱代表链，以及任何消费整个 `SphereFacts` 的 theorem；不应仅因投影暂未用到缺口就把整个包标为完成。

**本卡 closure：** 数学家选择并批准推导路线；Lean 证明同输入坐标桥梁及 span/zero 结论；相关 theorem 的实际依赖不经过 `sphere_facts` 本身或最终结论。
冻结记录：审查人 ______；日期 ______；选项/版本 ______；尚余前提 ______。

## M08-B：`y_not_hit` 是否需要无限页合同

### 目标、可用事实与未解决部分

`sphere_facts` 的第二处 `sorry` 在 [Computation/Route.lean](../KIP126/Main/Solution/Computation/Route.lean) 469 行，输出 `Derived.SphereFacts.y_not_hit`。
该字段定义于 [Route/Consequences.lean](../KIP126/Main/Solution/Computation/Route/Consequences.lean) 95 行，是对 Y 的 `NeverHit`，量化所有 `r ≥ 2`。
`NeverHit` 排除非零延续成为 incoming target；它并不保证 Y 存在任意后页延续，也不排除 Y 的 outgoing differential。
定义见 [Computation/Predicates.lean](../KIP126/Def/SpectralSequence/Computation/Predicates.lean)，47 行。
Y 的实际 bidegree 是 `(11,136)`；[SphereSurvival.lean](../KIP126/Main/Solution/Computation/Route/SphereSurvival.lean) 的 private `y_basis_label`（940 行）将它识别为该格的 basis index 3。
同文件 private `y_survives_five`（963 行）证明非零存活到 E₅；数据 row 2852 仅提供到 E₅ 的提升。
标准 `h₆²` 在 `(2,128)`；selected row 2314 仅给 `ReachesPage 7`，见 [Selected.lean](../KIP126/LinProgram/Route/Selected.lean) 808 行。
因此潜在 `d₉:(2,128)→(11,136)` 的次数完全吻合，E₇ 提升本身不能排除它。
原始 [Shard018.lean](../KIP126/LinProgram/Generated/Staircase/Shard018.lean) 的 row 2314 也是 level 9993；只切回完整表不会自动加强这个结论。

新基线已有局部 `y_incoming_source_zero_except_nine`（Route.lean 419 行）和 `y_not_hit_except_nine`（441 行）的证明体，排除了所有 `r ≠ 9`。
它们只使用同一个 `I` 的局部数据和页演算，未调用 `sphere_facts` 或最终结论；但仍封装在未完成的 `sphere_facts` 证明中，并非独立公共交付。
尚未交付的是实际 `d₉` 排除；这不是“`y_not_hit` 为假”的判定。
如果保留无限页合同，审查必须回答：较强 `h₆²` survival、零 differential、乘法矛盾或其他独立事实中的哪一个能完成它？
每条候选路线都要展开依赖：禁止借 Prop7.8、Prop7.9 或最终 permanence 回填，再供这些结果使用。

### 实际消费者需要的较窄结论

当前 Main 中字段的直接投影使用在 [NuNinth.lean](../KIP126/Main/Solution/Route/Section7/NuNinth.lean) 1936 行。
该处通过 private `nu9_not_boundary`，从无限页 `NeverHit` 推出 **Y 不属于 `B₆`**，用于 Q₉ 中 weight 131 的非零 detection。
具体只消费：

```lean
I.realization.sphere 11 136 KIP126.Computation.Near126.Y ∉
  PageRepresentatives.boundaries H SphereSpectrum 6 (11, 136)
```

这是候选窄接口，尚未写入 Lean。它保留实际边界子空间，不能替换成“E₂ label 非零”。
`B₆` 是截至 `d₆` 的累计边界子空间；定义见 [PageRepresentatives/Data.lean](../KIP126/Def/ClassicalAdams/PageRepresentatives/Data.lean) 54–56 行。
另一个足够的候选入口是非零 E₂ label 加 `NeverHitOnWindow E 2 6 (11,136) Y`；窗口定义见 [State/Predicates.lean](../KIP126/Def/SpectralSequence/Computation/State/Predicates.lean)。
这个有限窗口可从新基线的 `r ≠ 9` 分支提取；仍须形成独立声明，不能把整个未完成的 `sphere_facts` 当作它的证明。
它不能仅由 `SurvivesTo E 5` 推出，也不要求 Y 存活到 E₇。

### 供会议检查的有限证明路线

| incoming 页 | 源格 | 可核查的已有工作/待补工作 |
| --- | --- | --- |
| 2–4 | `(9,135)`、`(8,134)`、`(7,133)` | SphereSurvival 的三项 incoming 计算与 E₅ 非零论证；Route.lean 447–454 行用后页非零排除早页 incoming |
| 5 | `(6,132)` | [SphereIncoming.lean](../KIP126/Main/Solution/Computation/Route/SphereIncoming.lean) 2688 行 `t_incoming_t_incoming8_source_four` 已证明整格 E₄ 为零；Route.lean 429–430 行传到 E₅ |
| 6 | `(5,131)` | Route.lean 375 行 `source_six_zero` 用完整一维 basis 及已知 `d₂` 靶关系证明整格 E₆ 为零 |
| 9 | `(2,128)` | 对候选 `B₆` 接口不再需要；保留原 `NeverHit` 合同则仍是独立未解决义务 |

新进展使该方案不再缺第 5、6 页的源格排除；尚余工作是独立抽取、把有限窗口转换为 `Y ∉ B₆`，以及批准消费合同。
转换仍需复用/提取有限版代表元归纳；这包括累计边界，不能只排除单个给定 source。
可审查现有 `nu9_not_boundary` 中的 `nhb_represents_zero_iff_boundary` 与逐页归纳，再把 `NeverHit` 限定到实际使用窗口。

### 决策与 closure

1. **保留原合同：** 找到独立的 `d₉` 排除，接合现有其余页范围证明，继续交付 `NeverHit Y`。
2. **按消费范围缩小接口：** NuNinth 改为消费 `Y ∉ B₆`，并把 `SphereFacts` 的相关聚合义务与有限消费者解耦。
选项 2 需要合同版本与 Blueprint 同步；原无限页命题是否属于论文要求，必须由数学家决定并记录，不能默默删除。
实施前还要检查 `SphereFacts` 的全部外部消费者、结构类型依赖和旧 `SphereSurvivalFacts` 接口，不能仅依据一次字段名搜索改变合同。
提出 `B₆` 替代不等于原 `NeverHit` 已被证明、解除或判为错误；本轮保留其未解决状态。
不要另建一棵平行的 stage witness/证明传递树；可使用普通 theorem 和显式有限前提组织现有 Solution。
**本卡 closure：** 批准数学范围；提交有限或无限所需的全部证明；NuNinth 的非零 detection 保持原强度；确认新依赖不包含最终结果。
冻结记录：审查人 ______；日期 ______；原合同保留/收窄 ______；论文覆盖处理 ______。

## M16 / M19：Toda 与弱代表构造、Cν 矛盾与 Proposition 7.9

现有 [MainToda.lean](../KIP126/Main/Solution/Route/Section7/MainToda.lean) 的 `main_toda_bracket_detected`（28 行）与 [AnyY.lean](../KIP126/Main/Solution/Route/Section7/AnyY.lean) 的 `any_y_h0_extension`（26 行）都 import `Section7.Final`。
它们的当前证明均为 `False.elim (c3_excludes_c5 hc3 hc5)`；这是条件矛盾的合法推论，不是独立构造步骤。
[ConditionalY.lean](../KIP126/Main/Solution/Route/Section7/ConditionalY.lean) 又 import MainToda；其状态也须按实际依赖判定。
因此不能把这三个现有 proof body 作为 Prop7.9 的上游 milestone；不存在 Lean import 循环，但照抄论文图会制造任务图循环。
Blueprint 的相关节点在 [near126.tex](../blueprint/src/chapters/near126.tex)：`lem:toda-two-extension`、`cor:near126-two-extension`、`prop:near126-c3-not-c5`。

当前独立证明入口是 `KIP126.Main.Solution.Route.Section7.target_nu_divisible`，见 [NuTarget.lean](../KIP126/Main/Solution/Route/Section7/NuTarget.lean) 62 行；新版本仍走同一弱代表链。
其实际组织应记录为以下相接的工作包，而不是将 MainToda/AnyY 提前：

| 工作包 | 现有源码与输出 |
| --- | --- |
| α₁ 与 bracket 非空 | [AlphaOne.lean](../KIP126/Main/Solution/Route/AlphaOne.lean)、[TodaNonempty.lean](../KIP126/Main/Solution/Route/Section7/TodaNonempty.lean) |
| 严格目标与初始非零 | [AnyYHelpers.lean](../KIP126/Main/Solution/Route/Section7/AnyYHelpers.lean)、[WeakInitialNonzero.lean](../KIP126/Main/Solution/Route/Section7/WeakInitialNonzero.lean) |
| 低 filtration 修正 | [ThetaToda.lean](../KIP126/Main/Solution/Route/Section7/ThetaToda.lean)、[ThetaShuffle.lean](../KIP126/Main/Solution/Route/Section7/ThetaShuffle.lean)、[WeakRepresentative.lean](../KIP126/Main/Solution/Route/Section7/WeakRepresentative.lean)；保持 `λ² h₀ y ≠ 0` |
| Y detection 与 ν 整除 | [WeakYDetection.lean](../KIP126/Main/Solution/Route/Section7/WeakYDetection.lean)、[NuTargetHelpers.lean](../KIP126/Main/Solution/Route/Section7/NuTargetHelpers.lean)，消费独立 NuExtension9 |
| Cν 矛盾 | [CnuRigidity.lean](../KIP126/Main/Solution/Route/Section7/CnuRigidity.lean) 528 行 → [Final.lean](../KIP126/Main/Solution/Route/Section7/Final.lean) 34 行；与 [CofiberAndFiltration.lean](../KIP126/Main/Solution/Computation/Route/CofiberAndFiltration.lean) 720 行 `cnu_target_through5` 的独立 incoming 2–5 排除相矛盾 |

跨文件 private helper 不宜全部公开；优先提取“存在 filtration ≥11 的 y 且 `λ²h₀y≠0`”与“这样的 y 被指定 Y 检测”两个精确输出。
现有 private 入口分别为 `main_weak_high_representative`（WeakRepresentative.lean 2631 行）和 `weak_y_detected_from_low`（WeakYDetection.lean 2570 行）。
将它们公开仍是候选方案；须保留现有参数、同一 quotient、检测的非零要求和实际 λ 次数，不能先作“任选代表元”加强。
决策：采用现有弱代表链并把 MainToda/AnyY 标为下游 corollary，或单独要求独立重现其论文推导。
后一选项的 proof 必须禁止依赖 `c3_excludes_c5`；已有 ex-falso body 不能充当独立交付证据。
**本卡 closure：** 明确选择；导出的任务依赖与 proof constants 方向一致；核对 M08、M09–M11、Toda/source adapters 的局部证明与传递依赖状态没有被聚合标记掩盖。

## M20：同一显式 input 与最终目标合同

现有 `KIP126.Main.Solution.Route.proposition_7_8 (input : Challenge2)` 已显式接收一个输入，见 [Selected.lean](../KIP126/Main/Solution/Route/Selected.lean) 54 行；大段局部证明已拆入 `Route/Selected/`。
但 `proposition_7_9`（46 行）和多数 §7 公共 theorem 使用 [StageInput.lean](../KIP126/Main/Solution/StageInput.lean) 的固定 `witness`（35 行）投影。
最终 [Solution/h6_sq_permanent.lean](../KIP126/Main/Solution/h6_sq_permanent.lean) 22 行仍是无参数的标准命题，当前借助唯一开发 axiom `Main.Axiom.challenge2`。
新基线已实现 `nuSourceResults`（StageInput.lean 2011 行）的实际 ν 悬挂方块证明，核心 helper 是 `selected_nu_suspension_square`（1284 行）；不再列为直接 `sorry`。
仍有 `todaSecondaryComparison`（267 行）的低 Toda 值与任意二阶 θ 的对称 Toda 比较缺口（281、289 行）。
[SourceConsequences.lean](../KIP126/Main/Solution/Literature/Route/SourceConsequences.lean) 的 `route_moss`（182 行）与 `eInfty_shift_natural`（193 行）仍分别在 186、254 行有直接缺口。
这些证明进展不自动解决显式输入组织，也不证明传递依赖已闭合。
数学家需要先批准一个**内部**条件组合合同：文献、计算、labels、tmf binding 从同一显式 `input` 投影，均作用于 Def 固定的同一 route、quotient 与 ν。
建议内部 theorem 的形状是 `∀ input : Challenge2, NonzeroSurvival sphereAdamsData (2,128) standardH6Square`；这只是提案，尚未添加声明。
Prop7.9 及其实际消费者应同步参数化或等价重组；不能只把最终 wrapper 加一个未使用的 `input` 参数。
这不要求新 axiom、新 Challenge2 字段或一套重复 witness；也不能允许两个输入分别给出相同标签名却不同解释。

当前唯一 [Challenge/h6_sq_permanent.lean](../KIP126/Main/Challenge/h6_sq_permanent.lean) / Solution 配对的无参数合同必须保持逐字等型，直到负责人批准版本调整。
显式条件 theorem 本身不自动消除无参数 wrapper 的开发 axiom；需进一步说明如何从保留的外部数学前提构造或接收 input。
最终验收的外部前提、固定 foundation 尚余义务及 `#print axioms` 要求仍按 PROJECT_BOUNDARY 执行。
`C3` 是有实际 E₆ 代表元的零 differential；`D12` 要求 E₁₂ 靶非零；`C4` 非零 detection 与 `C5` 普通 detection 不能混同。
定义见 [Conditions/Predicates.lean](../KIP126/Def/Kervaire/Route/Conditions/Predicates.lean)，Blueprint 见 [h6_target.tex](../blueprint/src/chapters/h6_target.tex) 与 `prop:possible-h-6-sq`。
**本卡 closure：** 签名、参数与目标强度获批；Challenge/Solution 版本一致；所有 Main 消费者使用同一个 input；最终依赖审计排除开发 axiom 与 `sorryAx`。

## M09–M11：论文工具的数学假设审核卡

三者都是 Main 内部证明义务。Interface 的 [LinProgram/Rules.lean](../KIP126/Interface/Solution/LinProgram/Rules.lean) 可将它们用于计算规则认证；它们不能再消费由这些规则认证出来的同批结果。
M09、M10 当前仍有直接 `sorry`；M11 已有无直接 `sorry` 的局部证明体，但其 crossing 合同发生实质变化。三者均须展开命题审核，不能只批准一个 `...Law` 名称。

| 项目 | 现有 theorem / 直接缺口 | 数学家逐项确认 |
| --- | --- | --- |
| M09 Generalized Leibniz | `KIP126.Main.Solution.Tools.generalizedLeibniz`，[GeneralizedLeibniz.lean](../KIP126/Main/Solution/Tools/GeneralizedLeibniz.lean) 94 行；110、158 行缺口 | `page≤r`、`e(f)≤m≤page−2+e(f)`、`e(f)≤l`；所有 cycle/permanent 前提；source crossing 二择一及 target no-crossing；输出 `d_(r+l−m)(y)=y∞`、靶次数 `(s+r+l,t+r+l−1)` |
| M10 Generalized Mahowald | `KIP126.Main.Solution.Tools.generalizedMahowald`，[GeneralizedMahowald.lean](../KIP126/Main/Solution/Tools/GeneralizedMahowald.lean) 2943 行；3321、3362 行缺口 | 真实三角、normalized exponent 和=1、actual suspension label；第二 no-crossing 分支属于 Z 的 differential；输出存在 `y′` 且模真实 `B_r′` 同余，不能加强成固定 y 严格相等 |
| M11 finite stretching | `KIP126.Main.Solution.Tools.finitePageExtensionStretching`，[PageExtensionStretching.lean](../KIP126/Main/Solution/Tools/PageExtensionStretching.lean) 1171 行；该文件无直接 `sorry` | 后页 cycle 前提不变；新障碍在同一早有限商内保持 weight/λ 层，包含非 essential 的非零较短 extension；只得后页解存在，不得任意指定解可提升、相容解塔或无限 extension |

陈述展开分别见 Def 的 [GeneralizedLeibniz](../KIP126/Def/Kervaire/Route/Tools/GeneralizedLeibniz.lean)、[GeneralizedMahowald](../KIP126/Def/Kervaire/Route/Tools/GeneralizedMahowald.lean)、[PageExtensionStretching](../KIP126/Def/Kervaire/Route/Tools/PageExtensionStretching.lean)。
论文对应 [MainPaper/main.tex](../MainPaper/main.tex) 的 `thm:e73f481e`、`thm:158d451a`、`prop:dec738d3` / `cor:dfc6043e`；Blueprint 见 [generalized_tools.tex](../blueprint/src/chapters/generalized_tools.tex)。
GL 的两段工作仍是 cycle 延续与 δ/Bockstein label 模边界比较。
GM 的 MH1 已处理靶属于 `B_q`、`q=1` 及 `T.Z=.sphere` 的分支；剩余 3321 行是 `q>1`、靶不属于 `B_q`、`T.Z≠.sphere` 的实际 δ 比较。3362 行仍需 May 边界 lift 与有限 `B_(n+m+l−(m−e(g)))` 同余，含符号与 mod-2 label 比较。
M11 必须重审 [FiniteExtensionNonliftableCrossing](../KIP126/Def/Kervaire/Route/Extensions/Stretching/Predicates.lean) 28 行：source 不在实际后商→早商的 `ρ` 所诱导 E∞ 像中；`b=0`、长度零也包括在候选内；不能换回旧版较小商中的 essential crossing。
新 M11 不声称与旧谓词或论文印出的推论等价；计算 replay 还须逐例证明新前提，不能以只排除 essential crossings 的证书替代。局部 proof 无 `sorry` 仍不等于数学家认可或传递依赖已闭合。
GM 真实消费链还包括 NuFifth → NuNinth → M19；GL/stretching 的证书消费者应在接口清单中单独记录。
**各卡 closure：** 假设及结论与论文范围获批；所有 degrees、λ exponents、representative 与 no-crossing 使用一致；tool theorem 的证明独立于其认证的 computation results。

## 会后应形成的决定

- M08-A：选择一般推导、现有完整同输入桥梁或 selected 数据扩充，并明确需要版本化的签名。
- M08-B：明确无限页 `NeverHit` 的独立证明路线，或批准有限 `B₆` 消费合同及原命题的覆盖安排。
- M16/M19：批准弱代表任务链；逐一标记由最终矛盾导出的条件 corollary。
- M20：批准内部显式 same-input 合同与现有无参数最终合同之间的迁移/组合方式。
- M09–M11：分别记录数学审查人与签名版本；未完成的证明和传递依赖继续显式保留。

上述决定完成前，允许准备独立 proof 工作和候选声明；不得将本审查包或自动检查结果记作“数学家已认可”。
