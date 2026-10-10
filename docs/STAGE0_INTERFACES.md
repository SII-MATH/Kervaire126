# 第0步数学接口与证明责任

第0步要求准确确定数学语言、对象来源、次数、条件、范围和证明责任。它允许明确的模型构造、比较、认证和本文证明暂用 `sorry`，不允许弱化目标、无来源新增假设或在模型中预设本文结论。目录职责以 [AGENTS.md](../AGENTS.md) 和 [PROJECT_BOUNDARY.md](../PROJECT_BOUNDARY.md) 为准。

历史修正报告中的验收结论限于当时检查的范围。目前完整第0步仍有文献覆盖、来源忠实性等待核验项，不能冻结 Literature 或宣称全体接口验收完成。C₂/Cη 等计算认证中间谱按用户决定留给 Interface 的证明过程，不再列为 Challenge2 接口完整性缺口。已有声明、已完成证明和实际验证分别记录；统一输入结构不改变模型构造、计算认证和论文推导中的证明责任。

按用户 2026-10-06 的范围决定，导言中的叙述、推论和开放问题不再属于形式化计划；仍保留标准 h₆² 最终目标及正文证明需要的数学内容。当前目标止于标准 h₆² 的非零永久存活：流形模型、Browder/Pontryagin–Thom 几何比较、低维流形存在性及几何 HHR 不存在性不再属于 Challenge2 或当前验收。Blueprint 中导言专用的对应文献目标已删除，原文制品仅作归档来源记录。主路线需要的经典 θ₅ 存在、h₅² 检测与二阶性输入仍须交付；Hopf 映射、cofiber 和谱乘法等同伦模型义务也不受影响。

## 同一个 M 与标准 T

Def 内固定的基础必须有实际谱模型的实现/识别接口。来源不能只是另一个任意稳定范畴或一个未定义的 `isActualSpectrum : Prop`：具体 prespectrum、稳定等价及 HF₂-local 反射给出可审核的经典对象来源。论文引言明确 S⁰ 为 2-completed sphere，源另列这个单位与 Moore-2 完成的比较，未声称所有无界谱的两种完成相同。比较须关联球谱、悬移、cofiber、乘法、HF₂ 及其单位映射。构造与识别证明可以待补；比较的数学内容不能省略。

标准 Adams 塔来自同一 HF₂.unit。Milnor cooperation/cobar 坐标绑定实际第一页面及 d₁，并与 ring/Künneth/basis 比较。标准 h₆ 在 (s,t)=(1,64)，标准 h₆² 在 (2,128)，stem 分别63、126。最终目标是

```lean
NonzeroSurvival sphereAdamsData (2, 128) standardH6Square
```

这里存在同一个 Z∞ 代表，其 E₂ 像为指定标准类，E∞ 像非零。它不是只要求出微分为零、到有限页，或各页独立存在代表。该类型全部定义依赖只来自 Def 和基础库；A/C 只能进入证明。

实际同伦群仍是整数模，不因 E₂ 为 F₂ 向量空间而全体变为特征2。上同调 Hⁿ(X;E)=[X,ΣⁿE]=π₋ₙF(X,E)；UCT 的 Hₙ 与 Hⁿ 对应，Steenrod degree n 同样对应 π₋ₙF(HF₂,HF₂)。

## 统一 Challenge2

Def 固定经典实现、路线模型和共享数学背景，包括实际完成球、HF₂、Milnor 坐标及 tensor/cooperation 比较。`KIP126.Def.standardSphereApplicability` 对这个固定实现陈述实际球塔的 HF₂ nilpotent completeness 和强收敛，证明保留明确的 `sorry`；下游可直接引用其准确陈述。原 Challenge1 的实质义务仍在，但不是 Challenge2 字段。独立 Challenge1、重复 implementation 和相等运输已删除；countable-products 等结构仍来自固定实现。

Challenge2 顶层恰有 `literature` 和 `computation` 两项。`LiteratureInterface` 包含源对象、E∞ 同构选择及其比较的 `bindings`，以及依赖这些对象的 48 条直接数学声明 `results`；`ComputationInterface literature` 包含程序解释的 `bindings`，以及依赖同一文献包和计算绑定的七个顶层 `results` 字段。展开命题结构后，结果层共有 29 条声明；bindings 中另外有 4 条数学比较条件，坐标对象与包装字段不计为定理。固定 E₂ `presentation` 在计算绑定中，路线模型与其 background 则由 Def 预先固定，不再由 Challenge2 另选。Main 在取得同一见证后证明内部适配。`Interface/Solution/Literature/Route/SourceExistence.lean` 单独列出关联来源责任：从 Pstrągowski 的实际球面谱层构造及各项前人结果得到与固定路线相容的来源和文献结论。它不声称这里已经实现其 ∞-site；构造证明仍待补，不含 C、Application、high125 或本文新工具。

供人工逐项判断的汇总视图见[统一输入清单](challenge-input-inventory.html)。该 HTML 直接读取唯一机器清单 `external-inputs.json`；数学接口仍以 Lean 结构为准。文献结果只登记 `LiteratureResults` 的 48 条直接命题字段，不再登记 `adamsOneLine`、`route` 等包装字段或重复展开父子结构。Challenge2 文件只陈述两项交付，不定义便利转发或证明适配。正文使用的经典 Hopf 微分直接取对应字段；实际需要的路线消费视图由直接字段与 Main 的内部推论组装，未另选输入。E∞ 的三个 νX/有限商页面同构保留在 bindings；全 synthetic 对象的 weight 同构来自固定 Adams 塔构造，自然性在 Main 证明，不作为独立文献输入。BHS 的 λ/ρ 相容性与标签条件保留在 results。导言不再形式化：Adams 一线分类、完整 Hopf 存活 iff、May 低维乘积和平方存活均已删除；`adamsOneLine_other_degree` 的未使用生产声明也已删除。正文使用的 `adamsOneLine_d2` 保留，经典 `theta_5`/`h_5^2`、η/ν 检测和存活输入保留。参数化命题族按一个字段计数，字段内的合取不再拆分。来源、locator、制品和 declaration 对应关系全部在 JSON 中维护，不再编译一份 Lean 来源目录。Blueprint 已为这 48 条分别补写独立数学节点，保留量词、假设、次数和同一 bindings，并直接链接到相应 Lean 字段。唯一 JSON 清单逐条绑定 48 个不同节点；校验读取活跃章节，拒绝共用概述节点或误连字段。Moss 一般输入与 Main 局部应用、BR21 源方程与 Main 计算坐标推论已分开。该绑定不表示来源核验或证明完成；导言专用分类、几何结论及开放问题已移出当前形式化计划。归档文献制品保留作来源记录，不能当作当前 Challenge2 字段清单或已核实的完整外部定理集合。

计算的逐条 Blueprint 清单位于 `blueprint/src/chapters/computed_inputs.tex`，采用与文献清单相同的平面索引：29 条结果声明、4 条绑定比较条件，各自有独立数学节点和实际 Lean 投影链接。该章只保留这 33 条编号陈述；共享定义和示例在 `computation_schema.tex`，Main 内部推导计划在 `near126.tex`，附录转录和输出覆盖审计在 `coverage.tex`。唯一 JSON 清单在七个结果字段下登记具体 statement，在 `computation_binding_statements` 中登记四条比较；校验同时核对实际 Lean 结构的展开、独立节点和所属字段。人工 HTML 清单读取这些记录逐条展示，不再用七个包装字段代表定理条数。原始表中的每行不是额外的独立定理项，普通合取和参数化命题族仍按一条计算。全部节点保留未完成的交付状态；这次对齐不证明实际谱模型上的计算正确性。

附录的 401 条记录和 9 个空带目前是论文转录。实际数据库审计确认：375 条球谱表范围记录由完整 staircase 覆盖，26 条 Cν 表范围记录由选定路线覆盖，九个空带的全部 35 个双次数在完整 E₂ 数据中为空。但这不是 401 条纸面表达式和状态的逐条语义对应：选定切片只包含其中 376 条记录所在的双次数，且程序的有限页到达、未知目标和反证记录仍需表达式识别、线性代数及 Main 的永久存活证明。不能把纸面状态再作为独立外部输入。[本次核查](audits/linprogram-appendix-20261006.md)记录直接输出与内部推论的界线。

唯一临时阶段公理直接给出 `Main.Axiom.challenge2 : KIP126.Challenge2`；Main 不再经过 `Nonempty` 或 witness choice。生产者不得使用这一消费公理。完整 Challenge2 的构造须让计算包依赖同一文献来源与 Def 固定模型，不能分别选择不相干的模型或来源。固定球谱适用性与分离性是独立的 Def 证明责任。BHS 完成适用性、完成比较和 realization 比较由 `literature.bindings.route` 明确交付；Main 仍须证明一般 Moss 到局部 sphere 结论的特化、全 synthetic weight shift 自然性、Toda 二级运算比较与 ν 来源结论，再同已有来源陈述组装 `routeApplication`。这些未完成证明不能当作文献结果或程序输出。

来源的四层分别是 `Bindings`（相对于 Def 固定 background 的来源对象及比较）、`Statements`（这些对象上的前人结果）、`Application`（Main 待证的内部来源适配）、`Inputs`（供 Main 消费的组装结果）。`Inputs` 还需要 Main 独立证明的 tmf 高过滤结论，因此它既不等于纯 A，也不是 Challenge2 字段。无实际用途的旧 `Literature.Route.A = Nonempty Inputs` 包装已删除。

## C 的固定范围和语义

数据版本为 Zenodo 14875701 / v126.3.cw49。目标仓的大 Raw 文件可为 LFS pointer；只在实体字节与固定 SHA 一致时使用外部本地实体。`select-route.py --check` 检查筛选/解析/坐标可重复，不证明实际 Adams 命题。

当前 selected 保留648个次数、963个基向量、671条来源记录、73对乘积次数与4个 bottom maps。其中包括用于零群与穷尽性的空基，不因看起来没有元素就删除。忽略来源后可有相同 Statement 的重复 payload；这不是删除来源记录的理由。

| 所需事实 | 精确交付及责任 |
|---|---|
| 维数、零群、任意线性组合 | `BasisCorrect` 的实际 E₂ 与有限坐标模等价；同时给线性无关和生成。缺次数/越界/解码失败不当零。 |
| CSV 单项式与命名类 | `SphereBasisValue`、`LabelsCorrect`、`computation.results.route_presentation` 使用同一个 `computation.bindings.presentation`；标准目标的定义不依赖 CSV 标签。 |
| 乘法 | `ProductCorrect` 对所选 degree pairs 的所有元素成立；另外比较 cobar product、presentation product 与实际塔层乘法。指定平方身份不替代一般乘法。 |
| Cν 胞腔映射 | `BottomCorrect` 与 `TopCorrect` 使用同一几何 Hopf ν 的 actual cofiber ι/δ 与悬移比较。 |
| 日志与 staircase | 普通 differential、非零 differential、reach、boundary、refutation 分开。depth1根反证不是正向等式；深层分支必须保留祖先条件。 |
| 有限至无限 | level9000解释为到E1000。非零永久存活还需有限页非零、入微分排除及实际球塔消失线；滤过尾部还需经典分离性。 |
| 认证 | `CertifiedRealization` 七项是数学证明目标；接收七项证明的组装、从未完成总目标取字段、原始日志存在都不是认证实现。 |

论文主定理§7的逐段需求映射、原始行定位及覆盖状态见[主定理计算依赖对照](audits/main-paper-computation-inventory-20261003.md)，不纳入引言推论或教学示例。`Main/Solution/Computation/Route/Consequences.lean` 与 `Route.lean` 区分基础 C 和内部派生目标。原 `e5_high125_other` 已删除；AF15 与 AF18 的两个非零 d₅ 现有独立精确声明，保留为 Main 证明责任。`Computation/High125.lean` 改用实际 `π_(125,130)`：F15=F25、F26=0、λ¹⁰ 可除性及 λ²⁰G 的两元素穷尽，保留 BHS 比较、来源得到的 G 永久性和分离性前提。相关 Massey、不定性、crossing、候选穷尽和 quotient-lift 条件不能凭表名省略。

## 来源适用性与内部推导

- 球谱正 stem 消失线保留 `0<t-s<2s-3` 的实际 E₂ 结论；来源为 Ravenel 第二版 Thm3.4.5(a) 的保守弱化。它的模型运输与标准球塔分离性有独立生产责任，不能从有限 CSV 推断。
- BHS 有限商与无限结论分开。有限部分原文有更一般论证；永久 lift 与 filtration 比较必须保留所用完成/收敛条件。来源的适用性和到所选对象的运输使用同一完成映射、实际页面/ν 映射及精确像、滤过、λ 可除性比较。所选经典源采用论文的完成球；仍不把任意谱的不同完成概念无条件等同。
- BHS `cor:synth-ctau-ASS` (1)/(3) 的 `FiniteQuotientPageVanishing` 另交付 q>0、r≥2 的**所有有限页**零区：w>t 或 t−w≥q。`SyntheticSourceInputs` 与 `SyntheticInputs` 原样传递这一前人结果；E∞ 公式不代替 E₃/E₇ 零区。Q9 的 `π_(123,130)` 只有过滤7…15可能具有非零关联分次；结合实际ρ的过滤自然性和分离性可消去更高过滤。任何这类论证均不预设 λ⁹ 在一般 Q9 同伦群上作用为零。
- Def 固定 tmf detector 的目标谱对象及单位；文献绑定选定来源谱和 BR21 的源端点类，计算绑定给出这些类到所选 CSV 坐标的比较及乘法相容性。2-local 文献模型与所选完成对象的比较仍须明确。BMQ 图支持 π₆₂(tmf₍₂₎)=0，但实际同伦像非零不自动推出指定关联分次非零。high125 的永久存活由 Main 从来源、乘法比较、C、消失线和分离性推出，不随 Challenge2 的 Application 传递。
- `Computation/Lambda.lean` 为同一 synthetic tmf 单列 (62,64) 的全幂 λ 单射、实际 realization 单射、θ₅ 及 ηθ₅² 单位像为零的推导。所需低过滤 stem63 零群来自 `TmfSourceResults.low_filtration63`，不能套用球谱专用单射引理。这些结论仍是 Main 的证明责任。
- Xu 的“存在一个二阶 θ₅”、整个62-stem的指数2、任意选择的 synthetic 二阶性分开；BX 原式与论文 λ 规范化分开。
- May 保留边界负号；消去负号所需的指数2条件另列。Moss 保留 convergence、defining system、crossing 与不定性条件。Toda 的二级运算比较与 ν 的相容三角属于内部适配。
- image-J 与 BR21 手工种子不因 reason=M 成为程序证明。可选精确来源特化或独立数学证明；所选 Statement 已承担认证责任，不必为每行额外添加外部公理。
- 广义 Leibniz、广义 Mahowald、stretching、选择无关性、C₃/C₄/C₅ 关系及 Propositions7.8/7.9 都是本文证明。C₃需真实E₆代表，D₁₂需E₁₂非零，C₄非零检测与C₅允许零leading class的检测不能混淆。

`Main/Solution/Route/AlphaOne.lean` 明确列出 stem124 的低过滤 E∞ 消失、AF10/AF13全分量生成、θ₅²三分支、Q9/Q11的指定非零微分和实际ρ零像，以及兼容α₁的存在目标。`AlphaOneProperties` 保留同一Q11代表的真实Q9投影，对每个U代表分别选择α₂、α₃，并准确使用α₂的权重137。`Main/Solution/Route/Section7.lean` 单列Massey全不定性、Moss crossing、乘后Toda不定性、完整主要bracket检测、条件性d₅(Y)=0、任意Y代表的h₀扩张、Q5/Q9的ν关系和最终Cν incoming矛盾。这些是Main目标，不能变成基础模型字段或文献/计算输入；未独立命名的细分步骤仍须在相应证明中完成。

`ModuleTripleToda` 的实际箭头依次为球上的η、球上的h₀、最后到Q9的λ³α₁，Toda悬移后落在π_(125,132)Q9。这保留π_(124,130)(Q9)·η与(λ³α₁)·π_(2,3)(S)两项不定性；最初把α₁放在第一条箭头会产生额外End(Q9)不定性的定义已修正。次数能够编译不代替这一语义检查。

Generalized Mahowald 在此处的实际参数为 n=3、m=l=0、r=r′=3。正文写出的E2零长度top extension须沿实际页面/循环比较适配到工具所需E3；Cν无crossing的精确目标是 `NoCrossingOn 3 3 (8,134)`，唯一潜在crossing为d₂:(9,135)→(11,136)，由完整五维空间排除。最终ν关系的Q3到Q5提升仍须处理全部AF10 correction，不能因为已有Q3关系就省略。

计算的某些原始推导使用本文新规则、窗口外的谱或 tmf。选择重放这条路径时，须先取得独立规则证明及其全部前提；不得用同一待认证 C 或最终 T 证明规则，再回头认证 C。其他直接证明路径仍可采用。通用规则证明不应接收整个 Challenge2 或包含 high125 内部推论的消费总包。

## C₂/Cη：Interface 证明内部依赖

Cη 顶胞腔自然性记录 462481 参与 `lem:x_123_9` 所用球谱 d₃ 的程序推导；C₂ 的 filtration-1 映射记录 212838 参与 `lem:nuext125` 所用 Cν d₃ 的程序推导。这两条最终微分结论已经纳入 C。当前 Route 数据解释只含 Main 直接消费的 S⁰/Cν，不因此遗漏这两条输入；但输入陈述存在也不代表计算认证已完成。

按用户决定，现在不补 C₂/Cη 的交付接口，也不增加 Challenge2 字段。这两个谱是否需要展开，由 Interface 证明同一最终计算命题时选择的路线决定：若重放上述程序路径，再按需构造 C₂=cofiber(2:S⁰→S⁰)、Cη=cofiber(η:S¹→S⁰)，并处理具体映射、源数据、坐标比较和证明；若采用独立证明，可以不经过它们。可复用的数学语言仍归 Def，固定制品及参数化解释仍归 LinProgram；不必为证明中的中间对象另建公共输入包。

历史报告将这些认证中间依赖列为第0步接口缺口的判断，不再适用。最终 C 结论的认证责任仍属于 Interface，不能从 Main 已承认的 C 倒推其正确性；其他文献覆盖、来源忠实性和数学绑定问题也不因本次职责澄清自动通过验收。

## 验收与未完成证明

第0步分别检查语义、计算覆盖、外部结果覆盖、职责、传递性依赖、目录及实际编译。完整认证、全部来源重证和最终 T 的无 sorry 证明属于后续目标。原始来源尚未核实、明确性质缺少绑定，或尚无可信充分前提时，应记录为未完成/证据缺口，不用通过编译代替判断。

Challenge 目录按交付职责组织：`Literature/Delivery.lean` 直接陈述固定绑定和 48 条文献结果，`Literature/Source.lean` 保存生产这些结果所需的参数化来源对象与原始声明；`Computation/Delivery.lean` 直接陈述固定计算绑定及认证要求。来源到模型的内部应用与组装在 `Interface/Solution/Literature/Applications.lean`。通用分支语义和参数化解释认证分别在 `LinProgram/Interpretation/Branch/Predicates.lean` 与 `LinProgram/Interpretation/Route/Certification.lean`；绑定固定球谱的有界 E₂ 比较对象在 `Interface/Challenge/Computation/Presentation.lean`，固定 tmf 乘法条件仍归 Def。Challenge 下不再按 Sphere/Tmf 对象与 Route 用途混合分类；保留旧公开命名空间只用于维持现有声明名，文件归属以清单为准。

## 定义、计算与来源的文件归属

通用数学对象与参数化数学接口均可留在 Def；分层依据是依赖和职责，而不是声明使用 `def` 还是 `structure`。Def 的传递依赖不得进入 LinProgram、Interface 或 Main。以下路径均相对于 `KIP126/`：

| 原路径 | 当前归属 |
| --- | --- |
| `LinProgram/Interpretation/AdamsE2.lean` | `Def/AdamsE2/Input/Data.lean`；通用 E₂ presentation 输入随远程 develop 的调整保留在 Def |
| `Def/AdamsE2/LinModel`、`LinClasses`、`LinProduct`、`LinBasisTable/Data.lean` | `LinProgram/Model/{E2,Classes,Product,BasisTable}` |
| `Def/AdamsE2/LinCompute` | `LinProgram/Compute/E2` |
| `Def/AdamsE2/LinComputedPolynomial`、`LinExpression`、`LinExpressionValue`、`Classes` | `LinProgram/Interpretation/{Polynomial,Expression,Expression/Value,AdamsE2/Classes}` |
| `Def/AdamsE2/LinAutomation` | `LinProgram/Tactic/Support` |
| `Def/AdamsE2/LinBasisTable/Predicates.lean`、`LinBasisTable/Certification`、`LinSquareDetection` | `LinProgram/Certificates/{BasisTable,SquareDetection}` |
| `Def/ClassicalAdams/LinE2Presentation/Data.lean` | `Interface/Challenge/Computation/Presentation.lean` |
| `Def/References/Literature/EtaRows/Data.lean` | `Interface/Challenge/Literature/EtaRows.lean` |
| `Def/References/Literature/AppendixTable` | `LinProgram/SourceMetadata/AppendixTable` |
| `Def/Comparison/StageInterfaces.lean` 及其 `Proofs` | `Def/Comparison/{Pages,ClassicalSynthetic/EInfty,ClassicalSynthetic/FiniteBockstein,PageExtension,Cobar}`，按主题组织定义和证明；`Def/Comparison/Interfaces.lean` 汇总通用接口 |
| `Def/Comparison/StageInterfaces/Models.lean` | `Def/ClassicalAdams/Moss/Context/Data.lean` 与 `Def/ClassicalAdams/Tmf/Model/Binding/Data.lean` |

迁移保留声明名、数学陈述和证明内容；旧公开命名空间如 `KIP126.Challenge2`、`KIP126.Def.Comparison.StageInterfaces` 不随文件改名。旧模块路径不保留单模块转发文件，直接使用新 import。`KIP126.lean` 继续汇总原有公开内容，`KIP126/Def.lean` 只汇总 Def 模块。

`LinProgram/SourceMetadata` 中的附录表抄录用于来源核对，不是来源清单的第二权威，也不能直接充当数学证明；规范来源清单仍为 `docs/external-inputs.json`。这些记录随 Lin 计算资料一起组织，不单设顶层 SourceMetadata 目录。`scripts/test_stage_boundary_layout.py` 检查上述传递依赖边界、导入完整性与无环性。

数学接口以当前 Lean 源码为准，来源、locator 与声明对应关系以 [external-inputs.json](external-inputs.json) 为准。保留的来源审查与计算依赖表是注明日期的检查证据，不是另一份权威清单；旧迁移、集成和验收记录可从 Git 历史追溯，不能沿用其完成结论。
