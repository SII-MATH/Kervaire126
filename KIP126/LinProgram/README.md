# Lin program data and interpretation

The program pipeline imports pinned external computations. It does not construct
the standard sphere Adams sequence or establish the final survival theorem.

| Directory | Responsibility |
| --- | --- |
| `Raw/` | Archived CSV, database and log inputs, with the extraction manifest. |
| `Translate/` | Deterministic translation and fixed-input checks. |
| `Generated/` | Lean encodings of the imported records. |
| `Route/` | Selection of the fixed records used by the proof route. |
| `SourceMetadata/AppendixTable/` | Typed transcription of the paper tables, with row labels and locators; recorded statuses require mathematical justification. |
| `Model/E2/Native/` | The quotient by all original CSV relations, its full grading, and the proved comparison with the legacy truncation through degree 261. |
| `Model/E2/`, `Model/Classes/`, `Model/Product/` | The legacy truncated quotient and its existing coordinate operations and elements. |
| `Certificates/RelationCatalogue/` | Kernel-checked homogeneity of every original sphere relation. |
| `Model/BasisCatalogue/`, `Certificates/BasisCertification/` | Imported basis values and coordinates conditional on explicit basis certification. |
| `Compute/E2/`, `Tactic/Support/`, `Interpretation/Polynomial/`, `Interpretation/Expression/` | Parsing, reduction, expression interpretation and calculation support. |
| `Interpretation/` | Mathematical interpretation parameterized by a supplied model. |
| `Certificates/Verifier.lean`, `Tactic/LinCert.lean` | Certificate contracts and the generic `lin_cert` tactic. |
| `Certificates/NamedElements/` | Polynomial and module-expression checkers and their evaluation soundness proofs. |
| `Certificates/Naturality/`, `Generated/Naturality/` | Fixed map-word and finite cochain batches, with replay via `Translate/replay-naturality-batch.py`; actual-map comparisons remain in Interface. |
| `Certificates/Milnor/` | Executable Milnor calculations, grading and rank bounds, and their soundness proofs. |
| Other `Certificates/` and `Tactic/` modules | Local fixed-data certificates and project calculation tactics. |

Generic E₂ table, page-algebra, presentation and input definitions belong to
`KIP126/Def/AdamsE2/`. The program-specific comparison with Def's fixed sphere
page is `KIP126/Interface/Challenge/Computation/Presentation.lean`.
`Interface/Challenge/Computation/Delivery.lean` specifies the correlated bindings
and results; `Interface/Solution/LinProgram/` constructs their certificates.
Main consumes those results from the same Challenge2 witness.

`KIP126.LinE2.NativeAlgebra` quotients by the original CSV relations only;
it adds no high-degree zeros. The old `KIP126.LinE2.E2` retains its degree-261
truncation as a compatibility model. The natural quotient between them is
proved to be an isomorphism on every component with internal degree at most 261.
Neither algebra is defined to be the actual sphere E₂ page.

The sphere presentation now contains one global graded F₂ algebra map from
`NativeAlgebra` to the direct sum of the same fixed actual E₂ groups, and
bijectivity through degree 261. Its old `comparison`, `product`, and
`comparison_mul` APIs are derived from this map and the truncation comparison.
The actual target product is fixed independently in Def; its named unfinished
ring-law proofs remain explicit. The construction of the global comparison,
basis, actual tower-product comparison, differential, staircase and route
conditions remain mathematical obligations. In particular,
a staircase threshold alone does not prove nonzero permanent survival.

The relocation from `Def/AdamsE2/Lin*` preserves public declaration names and
proof status. The admitted `coordinateCheck_sound` and unfinished Interface
certifications remain unfinished. Successful import, hash checks, calculation
or compilation do not establish their mathematical correctness.

Source identities, locators, versions and hashes are recorded in the canonical
`docs/external-inputs.json` manifest; this README introduces no source registry
or additional assumptions.

## Independence from the research attempt

The top-level `Lin-program/` remains an independent research project. KIP126
owns the certificate modules it uses; its build does not import modules or
take source roots from that directory. The adopted modules are ordinary parts
of the existing `KIP126` Lake library, with no additional shared package.

The initial adoption copies the complete 20-module dependency closure of the
three certificate libraries used at commit
`0cacf987437cfeff3f5c067a7a025182648516e0`. The source paths below are relative
to `Lin-program/program/`; the destination paths are relative to this directory.

| Research source | KIP126-owned location | Responsibility |
| --- | --- | --- |
| `LinProgramCertificates/Verifier.lean` | `Certificates/Verifier.lean` | Bind a certificate type, executable check and soundness theorem to a proposition. |
| `LinProgramCertificates/Tactic.lean` | `Tactic/LinCert.lean` | Apply the checked soundness theorem through `lin_cert`. |
| `NamedElementCertificates/{Basic,Evaluation,ModuleEvaluation}.lean` | `Certificates/NamedElements/` | Verify relation witnesses and interpret the resulting polynomial or module equalities. |
| The 15 selected `MilnorCertificates/` modules | `Certificates/Milnor/` | Certify the finite Milnor computations used by the secondary calculation support. |

Only import paths and one inherited trailing space change during adoption.
Public declaration names, including
`LinProgramCertificates`, `NamedElementCertificates` and `MilnorCertificates`
namespaces, are retained; they do not denote a dependency on the old project.
The original Lean source tree is unchanged; its README links to the adopted modules. Later changes in that tree do not
automatically change the KIP126 copies.

Some data-reconstruction scripts still locate the archived input under
`Lin-program/program/upstream/`. This adoption removes the Lean source
dependency; input locations and historical provenance records are unchanged.

These support modules depend only on Lean, Mathlib and one another. Concrete
inputs and certificates remain in the other LinProgram modules; comparison
with the fixed mathematical objects remains in Interface. Moving the support
code does not construct the bounded presentation or prove an actual Adams
differential. Historical audit paths and proof-completion statuses are retained.

## 任务归属与继续开发入口

本节按任务书中的工作解释代码归属；数学陈述与依赖以
[Blueprint 的 computation_schema 章节](../../blueprint/src/chapters/computation_schema.tex)
为准，逐次重放结果见[执行审计](../../docs/audits/linprogram-certificate/README.md)。
下面标为“规划”的目录尚未建立，等有具体实现时再创建，不用空模块表示进度。

### 验证器与具体证书

采用代码的来源与路径见上面的 Independence 小节。验证器和具体输入分开维护：

| 职责 | 归属 | 与后续任务的关系 |
| --- | --- | --- |
| 检查器合同及执行 tactic | `Certificates/Verifier.lean`、`Tactic/LinCert.lean` | 用“检查通过推出语义命题”的可靠性定理接收见证。 |
| 可复用的证书验证器 | `Certificates/NamedElements/`、`Certificates/Milnor/` | 认证多项式、模表达式及有限 Milnor 计算；后续数据证书复用这些模块。 |
| 固定输入的具体证书 | `Certificates/Products/`、`ModuleMaps/`、`Secondary/` 等 | 证明指定数据中的等式，调用上面的验证器；实际模型比较由 Interface 完成。 |

可复用的验证器不因“通用”二字就全部移入 Def：围绕计算编码、可执行检查和
证书格式的实现由 LinProgram 维护；不依赖这些编码的数学对象和定理才按主题放 Def。
`Certificates/Milnor/` 是底层计算验证器，`Certificates/Secondary/Milnor/`
服务 secondary 的展开、乘积表和计算支持，二者不是同一份库的重复命名。

公开 namespace 保留不代表仍有旧路径 import。源码路径与依赖变化后，三个完整
重放入口的历史编译收据必须按完整输入键重新核验，不能直接沿用旧完成计数。

### 四层职责

| 层 | 要回答的问题 | 放置位置 |
| --- | --- | --- |
| 通用数学 | 不依赖哪份 Lin 数据，数学对象、比较和规则本身如何定义或证明？ | `KIP126/Def/`，按 Steenrod、谱序列、ClassicalAdams 等主题组织。 |
| 原生数据与证书 | 如何可靠检查证书？这份固定输入表示什么？数据等式、原生映射和日志推理是否合法？ | `KIP126/LinProgram/`；解释可参数化于模型，不选择 Def 的固定球面模型。 |
| 固定模型认证 | 这些数据为何对应项目指定的球面、映射和微分？ | `KIP126/Interface/Challenge/Computation/` 定义交付合同，`Interface/Solution/LinProgram/` 构造比较、落实前提并证明结论。 |
| 论文消费 | 如何从同一个 Challenge2 中的结论推出论文结果？ | `KIP126/Main/Solution/`。 |

导入方向是 `Interface → LinProgram → Def`，Interface 也可直接导入 Def。
`LinProgram/` 不导入 Interface；`Interface/Solution/LinProgram/` 中的 LinProgram
只表示接入对象，其所属层仍是 Interface。例如 `a * b = c` 的数据证明在前者，
构造 P 并得到实际球面上的对应等式在后者。使用给定 P 的条件定理不等于构造 P。

证明责任按“数据 → 固定模型认证 → 论文消费”推进，通用数学支持前面各层。
这不是声称现有 import 图完全是一条链：`Interface/Solution/LinProgram/Rules.lean`
仍引用 `Main/Solution/Tools/` 中不读取计算交付的论文规则。
若后续抽取其中可复用的通用证明，应放回 Def；不能让计算认证依赖消费同一交付的结论。

### 每项后续工作放在哪里

以下缩写：`L = KIP126/LinProgram/`，`I = KIP126/Interface/Solution/LinProgram/`。
表中的“已有”只表示文件存在，不表示其中的所有数学义务已经完成。

| 工作 | 已有入口 | 后续归属与完成边界 |
| --- | --- | --- |
| 固定输入、原生 statement 与坐标 | `L/Raw/`、`Translate/native-contract.py`、`Generated/NativeContract/`、`Interpretation/Differentials/`、`Interpretation/State/` | 原生记录和解码留在 L；绑定到固定模型的结论留在 Interface。论文别名和进一步推论在 Lean 中处理。 |
| 数据商代数、关系与基底 | `L/Model/E2/`、`Model/BasisCatalogue/`、`Certificates/BasisCertification/`；`I/Basis/Certification.lean`、`Comparison.lean` | 商代数内的张成、独立性及证书属于 L；通过实际比较传到球面属于 I。现有 `basisTable_correct` 仍位于 I 且未完成，后续数据侧证明应在 L 完成，再由此入口调用。 |
| Cη→球面、CW→Cη 原生映射 | `L/Model/ModulePresentation/`、`Certificates/ModuleMaps/`、`Translate/module-map-certificates/` | 全量关系见证与商映射证明留在 L；与实际谱映射的比较留在 `I/Naturality/`。 |
| secondary 5487 | `L/Certificates/Secondary/`、`Translate/secondary-seed5487-certificates/` | 固定复合式和辅助见证留在 L；一般 secondary 运算定理按主题放 Def；与实际球面 d₂ 的接入放 I（规划 `Secondary/`）。 |
| 自然性 245131、462481 | `L/Certificates/Naturality/`；`I/Naturality/Row245131.lean`、`Row462481.lean`、`CWModel.lean`、`CWToCeta.lean` | 坐标等式留在 L；实际对象、来源微分、映射比较和整条认证链留在 I。Cη、CW 是认证过程的对象，不增加 Challenge2 根字段。 |
| 分支 152097→152098 | `L/Interpretation/Branch/`、`Certificates/Products/Trial152097*.lean`；`I/Products/Trial152097.lean` | 通用候选覆盖/排除解释留在 L；固定球面上的覆盖、非边界性、到达 E₄ 和最终排除放 I（规划 `Branch/`）。 |
| 高页乘法与高级规则 | `Def/ClassicalAdams/TowerLongLayer/Pairing/`；`I/Rules.lean` | 通用乘法、边界相容性与 Leibniz 证明放 Def；对固定日志的前提核实与规则应用放 I。已有规则适配器不等于前提已落实。 |
| 消费者迁移和总交付 | `I/AdamsOneLine/H6.lean`、`I/Route/Certification.lean`；`Main/Solution/StageInput.lean`、`Main/Solution/Route/` | Interface 生产原生结论；Main 从同一 Challenge2 取出数据并推导论文结果；最终在 `Interface/Solution/Challenge2.lean` 组装。生产者不能读取待构造的总交付。 |

### P 的六步构造如何落到模块

`Interface/Challenge/Computation/Presentation.lean` 已定义 **P 必须满足的合同**；
`I/Multiplication.lean` 已声明存在性目标，但尚未构造 P。
下面是 Blueprint 六个开放节点的实现归属，不是新增六个条件参数。

| Blueprint 节点 | 实现归属 | 应交付的数学内容 |
| --- | --- | --- |
| `def:lin-native-representative-specification` | 输入恢复用 `L/Raw/`、`Translate/`、`Generated/`；数学对象规划在 `L/Model/Resolution/` | 原生分解、复形以及每个生成元对应的 cochain；明确三种编号和缺失记录。 |
| `prop:lin-native-resolution-correct` | 固定分解证书规划在 `L/Certificates/Resolution/`；通用分解比较复用 `Def/Steenrod/MilnorModule/` | 自由/投射性、微分平方零、增广、正合性和所需全部次数的覆盖。 |
| `prop:lin-native-generator-classes` | 原生类与运算放 `L/Model/Resolution/`，固定循环及乘法见证放 `L/Certificates/Resolution/`（规划） | 统一构造生成元的上同调类并认证乘法，不靠论文名称指定对应物。 |
| `prop:lin-native-actual-comparison` | 通用链比较放 Def；固定原生分解到指定球面的组装规划在 `I/Presentation/` | 对所有所需次数、所有循环成立的 Φ，以及代表元公式。 |
| `prop:lin-native-quotient-comparison` | 关系边界见证、数据基底及原生上同调比较放 L；复合 Φ 并构造 P 放 `I/Presentation/`（规划） | 从无截断 A 构造全局分次代数同态；同一个映射在全部 `s ∈ ℕ, t ≤ 261` 逐次满射、单射，包括空表次数。旧 D 坐标由已证低次等价派生。 |
| `prop:lin-native-actual-product` | 通用乘法比较复用 Def；固定球面相容性证明放 `I/Presentation/`（规划），接入现有 `I/Multiplication.lean` | 单位以及所有约定范围内实际代表元的乘法相容性。 |

不能把整个 P 构造都塞进 `Presentation.lean` 合同文件，也不能把实际球面比较放进 L。
旧 D 对 `t > 261` 的截断不能用来证明实际 E₂ 消失；新 A 的全局比较保乘性没有这个上界。新仓已有的通用比较结果应复用，
但其前提和固定模型依赖仍要逐项落实。

### 两个 Lin 目录、生成结果与历史记录

- 顶层 `Lin-program/` 是独立研究尝试，保存上游程序、资料、参考形式化和探索项目。主工程采用的 Lean 代码复制进 KIP126 自行维护，主库不从独立目录导入；某些固定制品仍是重建输入，不能整目录当作废弃内容删除。
- `KIP126/LinProgram/` 是本项目当前导入数据、解释与证书的实现入口。可移植的完整重放命令以这里两个 `Translate/*-certificates/README.md` 为准。
- 大批量运行产生的模块、缓存和收据保存在各命令指定的独立输出目录。`Generated/` 保存项目选定并登记的生成输入；一次运行成功不自动把临时结果纳入正式交付。
- Blueprint 记录数学计划；本 README 记录任务归属；`docs/external-inputs.json` 记录来源；`docs/audits/linprogram-certificate/` 记录检查与剩余前提。历史报告中的路径和计数保留当时含义。

新增代码时先判断它是否依赖固定 Lin 输入、是否选择实际固定模型、是否消费 Challenge2，
再按上表归类。模块只在有具体对象或证明时创建，保留公开声明名称；路径整理不改变证明状态。

## Finding a theorem by subject

The file path gives its subject and role. Public declaration names are retained
across file moves, so a namespace such as `KIP126.LinE2.OneLine` is a stable API
name, not a second file location. Import the concrete module below; there are no
one-module compatibility wrappers at the old paths.

| Subject | Data certificates | Fixed-model Interface |
| --- | --- | --- |
| Recorded basis versus certified basis | `Model/BasisCatalogue/Data.lean`; `Certificates/BasisCertification/{Predicates,Data,Proofs}.lean` | `Basis/Certification.lean` states the unfinished catalogue-correctness obligation; `Basis/Comparison.lean` transports it through the supplied comparison. |
| One-line d₂ row 5434, h₄ to h₀h₃² | `Certificates/AdamsOneLine/H4Source.lean`, `H4Target.lean` | `AdamsOneLine/H4.lean` |
| One-line d₂ row 5541, h₆ to h₀h₅² | `Certificates/AdamsOneLine/H6Coordinates.lean` | `AdamsOneLine/H6.lean` |
| Hopf class h₁ and η | `Certificates/Hopf/H1Coordinates.lean` | `Hopf/H1Comparison.lean` |
| Vanishing-target d₂ row 5432 | `Certificates/Differentials/Row5432Coordinates.lean` | `Differentials/VanishingD2.lean` |
| Trial 152097 products | `Certificates/Products/Trial152097.lean`, `Trial152097Coordinates.lean` | `Products/Trial152097.lean` |
| Naturality row 245131 | `Certificates/Naturality/Row245131Coordinates.lean` | `Naturality/Row245131Coordinates.lean`, `Row245131.lean` |
| Naturality row 462481 | `Certificates/Naturality/Row462481Coordinates.lean`; `Certificates/Products/Naturality462481.lean`, `Naturality462481Modules.lean` | `Naturality/Row462481.lean`; `Naturality/CWModel.lean`, `CWToCeta.lean` construct the same CW-to-Cη conditional chain. |

Interface paths in this table are relative to
`KIP126/Interface/Solution/LinProgram/`. The paths do not indicate that an
actual-model comparison or a recorded differential has been certified.

## Shared exhaustion proof

[Def/Algebra/TwoElement/Proofs.lean](../Def/Algebra/TwoElement/Proofs.lean)
proves that a vector in an F₂ singleton span is zero or the specified spanning
vector. It also proves, over every semiring, that a linear equivalence transports
that exhaustion and identifies any independently specified nonzero vector.
[Model/E2/Proofs.lean](Model/E2/Proofs.lean) specializes the span lemma to the
existing homogeneous data component. The h₁, h₄, h₀h₃², h₆, h₀h₅² and h₆² data and
Interface proofs reuse these lemmas; each case still proves its own full-degree
exhaustion and retains the same nonvanishing and literature inputs.

## Module path migration

The following table records file locations only. Names inside Lean declarations,
Blueprint labels, mathematical statements, input bytes and proof status are
preserved. Historical audit snapshots retain the file paths recorded when they
were produced, including the `module` locators in `row462481-trace.json`; use this
table to locate their declarations today. Archived hash reports and immutable
trace snapshots are not rewritten to pretend that a historical file had a new
path. Executable Lean imports and current replay commands use the new paths.

| Former module path | Current module path |
| --- | --- |
| `KIP126/LinProgram/Model/BasisTable/Data.lean` | `KIP126/LinProgram/Model/BasisCatalogue/Data.lean` |
| `KIP126/LinProgram/Certificates/BasisTable/Data.lean` | `KIP126/LinProgram/Certificates/BasisCertification/Data.lean` |
| `KIP126/LinProgram/Certificates/BasisTable/Predicates.lean` | `KIP126/LinProgram/Certificates/BasisCertification/Predicates.lean` |
| `KIP126/LinProgram/Certificates/BasisTable/Proofs.lean` | `KIP126/LinProgram/Certificates/BasisCertification/Proofs.lean` |
| `KIP126/Interface/Solution/LinProgram/BasisTable.lean` | `KIP126/Interface/Solution/LinProgram/Basis/Certification.lean` |
| `KIP126/Interface/Solution/LinProgram/SphereBasis.lean` | `KIP126/Interface/Solution/LinProgram/Basis/Comparison.lean` |
| `KIP126/LinProgram/Certificates/OneLine.lean` | `KIP126/LinProgram/Certificates/AdamsOneLine/H4Source.lean` |
| `KIP126/LinProgram/Certificates/OneLineTarget.lean` | `KIP126/LinProgram/Certificates/AdamsOneLine/H4Target.lean` |
| `KIP126/LinProgram/Certificates/OneLineH6.lean` | `KIP126/LinProgram/Certificates/AdamsOneLine/H6Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/OneLine.lean` | `KIP126/Interface/Solution/LinProgram/AdamsOneLine/H4.lean` |
| `KIP126/Interface/Solution/LinProgram/OneLineH6.lean` | `KIP126/Interface/Solution/LinProgram/AdamsOneLine/H6.lean` |
| `KIP126/LinProgram/Certificates/H1.lean` | `KIP126/LinProgram/Certificates/Hopf/H1Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/H1.lean` | `KIP126/Interface/Solution/LinProgram/Hopf/H1Comparison.lean` |
| `KIP126/LinProgram/Certificates/LowStem.lean` | `KIP126/LinProgram/Certificates/Differentials/Row5432Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/Differentials.lean` | `KIP126/Interface/Solution/LinProgram/Differentials/VanishingD2.lean` |
| `KIP126/LinProgram/Certificates/ReplayProducts.lean` | `KIP126/LinProgram/Certificates/Products/Trial152097.lean` |
| `KIP126/LinProgram/Certificates/ReplayCoordinates.lean` | `KIP126/LinProgram/Certificates/Products/Trial152097Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/ReplayProducts.lean` | `KIP126/Interface/Solution/LinProgram/Products/Trial152097.lean` |
| `KIP126/LinProgram/Certificates/NaturalityHighStemProducts.lean` | `KIP126/LinProgram/Certificates/Products/Naturality462481.lean` |
| `KIP126/LinProgram/Certificates/NaturalityModuleProducts.lean` | `KIP126/LinProgram/Certificates/Products/Naturality462481Modules.lean` |
| `KIP126/LinProgram/Certificates/NaturalityCoordinates.lean` | `KIP126/LinProgram/Certificates/Naturality/Row245131Coordinates.lean` |
| `KIP126/LinProgram/Certificates/NaturalityHighStemCoordinates.lean` | `KIP126/LinProgram/Certificates/Naturality/Row462481Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/Naturality.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/Row245131.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityCoordinates.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/Row245131Coordinates.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityHighStem.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/Row462481.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityCW.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/CWToCeta.lean` |
| `KIP126/Interface/Solution/LinProgram/NaturalityCW/Model.lean` | `KIP126/Interface/Solution/LinProgram/Naturality/CWModel.lean` |
