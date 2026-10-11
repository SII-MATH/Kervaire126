# λ-Bockstein 与 Adams 比较：已验证部分及剩余连接

本记录只依据 KIPBase 中的定义。最终谱序列同构尚未完成。
前期关于有限 λ 商和边缘谱序列起始页的证明位于 `Rigidity.lean` 和
`ExtensionSS.lean`。当前态射构造没有增加公理、`sorry`、比较假设或
滤过有界性条件。

## 当前态射构造的精确状态

`AdamsBocksteinMorphism.lean` 已有几何 cap 给出的源列页面映射、
Adams 微分像到 λ-Bockstein 微分像的映射，以及在
`SyntheticShiftCofiberCompatibility` 条件下的循环保持定理。
`AffineReindexedSinglePageMap.succPageMap` 现在只以当前页所有双次数上的
映射及微分交换式为输入，经短复形同调给出下一页映射；它不预设整条态射。
`AffineReindexedUnderlyingMorphism` 现定义仿射重编号后的逐双次数 `V → V`
pre-morphism；`ofVIsos` 从整族 `V` 同构取出这族态射，尚不附加微分或
`Z/B` 条件。当前 `canonicalLambdaBocksteinESS` 的 `r₀=0`，所以它的 `V`
仍按原始 ESS 编号；不能仅将它重命名为 E₂ 的 `V`。

尚未构造 `CanonicalAdamsToLambdaBocksteinMorphism` 的值。具体缺口是：
**不是缺 Adams 的 E₂ 计算。** `rigidity_free_lambda_pages` 给出自由 λ
的 Adams 页面描述，`einfty_nuX_mod_lambda` 给出有限 λ 商的 E₂ 描述。
`canonicalLambdaBocksteinE0SourceIsoSynAdamsE2Diagonal` 进一步把这些输入
接到 λ-Bockstein 原始 **第 0 页源列**。此前把这说成“E₂ 项没有”是错误的。
`canonicalAdamsE2ToLambdaBocksteinRawE0SourceMap` 已把该同构反向写成
实际态射。`adamsE2ToBocksteinE2SourceMapAtWeight` 则利用自由 λ 页同构，
把已有的对角源列 E₂ 态射扩展到每个权重；对角以上源项取零态射。
`adamsE2_d2_geometric_target` 把此前的几何微分定理在长度二处实例化：
同一 cap 给出 Adams `d₂` 的靶代表和 Bockstein `d₂` 的实际靶页面类。
`adamsE2_d2_comm_on_image` 把交换关系写在两边的微分像子群上。
这一步尚未定义 Adams 整个靶页面到 Bockstein 靶页面的映射。
这里的缺口来自当前比较对象的实际类型：`SyntheticExtensionCoreData.e0TargetIso`
把 Bockstein 原始第 0 页靶列识别为靶对象 Adams 的 **E∞**，而
`NuSynAdamsGeometricComparison.targetEquiv` 把 Adams 第 2 页靶类识别为
塔的相邻层商。几何定理只在该类是一个 `d₂` 的靶时给出 Bockstein 靶页面类。
因此 `adamsE2D2ImageMap` 已有定义，但不能将它直接当作整张 Adams
靶页的映射；要填满整页，须另证一个对任意靶类定义且与此像映射一致的
加法映射。现有声明中没有这条延拓定理，不能用代表选择冒充。
仍缺的是把这些已有同构按实际页号组装成
`CanonicalAdamsToLambdaBocksteinMorphism` 所要求的整页基例：现有几何映射
在每个生成元次数给出源列映射，目标列的任意页面类尚未得到映射；原始第 0 页
源列同构不能直接填入类型中要求的第 2 页到第 2 页映射。
此外，从当前页取同调得到下一页映射之后，仍需用几何微分公式证明新映射
与下一页微分交换，才能继续归纳。下面较早的“剩余”描述仅记录当时状态；
以上是当前已核对的缺口。

## 本次的页面微分基础

`AdamsBocksteinMorphism.lean` 现补出归纳的两个逐元素接口。
`synAdams_differential_eq_zero_iff_lambdaPow` 由 λ 乘法自然性和自由
λ 靶端的单射性证明：原 Adams 微分为零，当且仅当其有限 λ 幂重编号后的
微分为零。这给出循环条件的 λ 重编号步骤。另一方面，
`ElementPageRel.eq_zero_of_zero_source_relation` 证明零源 ESS 关系的靶
必在当前边界子对象中，故其页面类为零。这给出边界商中的靶端归零步骤。
二者将分别作为后续 `Zᵢ` 与 `Bᵢ` 归纳的页面接口。

几何 cap 端也已补出同一零条件的显式形式：
`capDifferential_mk_eq_zero_iff_exists_zero_source`。它把 cap 微分为零
等价改写为一条同长度、零源的相对圆盘关系，靶为原 divided target 的
指定 λ 幂。后续只需将该圆盘的靶页面代表与原 cap 的 λ-Bockstein 靶页面
代表比较，即可调用上述零源 ESS 引理。

`AdamsBocksteinMorphism.lean` 现把一个 λ-Bockstein 的发生关系同时
落实为源页面代表、靶页面代表和两者之间的页面微分：
`LambdaBocksteinOccursOn.exists_page_differential_reps`。靶页面代表记录
实际 λ 边界类，并已证明同一实际边界类至多给出一个靶页面类：
`LambdaBocksteinTargetPageRep.unique`。

由 Adams 微分导出的发生关系已接到这条引理：
`NuSynAdamsGeometricComparison.exists_page_differential_reps_of_adams_differential`。
因此，对一个给定的 Adams 微分，当前已有一条 λ-Bockstein 页面微分，且
其源、靶均带有实际过滤代表。接下来的工作是把源端识别为 E₂ 比较映射的值，
把靶端识别为 Adams 靶类对应的唯一页面类；两次唯一性识别给出页面微分交换。

页面递推现使用 `affineReindexedPageHomSucc`。它接受当前页的三项微分复形
之间的交换态射，并经同调商直接给出下一页态射。此处不要求当前页的比较
映射可逆，正符合从 E₂ 映射开始对 `Zᵢ`、`Bᵢ` 归纳的构造。

对每个给定的 Adams 微分，
`exists_targetRep_comm_of_adams_differential` 现在同时给出：该微分的
Adams 靶类在几何靶商中的表示、同一圆盘的实际 λ 边界靶页面代表、以及
源 E₂ 比较映射之后的 Bockstein 微分严格等于这个靶页面类。由此完成
“Adams 微分推出 λ-Bockstein 微分”的靶端识别。

边界部分现以
`adamsToBocksteinBoundaryPageHom` 表示。它定义为源比较映射后接
λ-Bockstein 页面微分；`adamsToBocksteinBoundaryPageHom_apply` 给出逐元素的
严格等式。这是 `Bᵢ` 归纳所需的边界映射。剩余的基例是证明源比较映射保持
循环，从而得到 `Zᵢ` 上的映射。

靶端零判据 `LambdaBocksteinTargetPageRep.eq_zero_of_mem_next` 已完成：实际
λ 边界进入下一过滤层时，其 λ-Bockstein 靶页面代表为零。这只是零类的一种
情形；靶页面也可能因入射边界而为零。循环保持的正确剩余步骤是：由 Adams
靶商中的零类，经自由 λ 的次数控制，得到 divided target 位于其边界子群；再把
该子群识别为 λ-Bockstein 靶页面的入射边界。不能把这一步替换为过滤层加一。
`lambdaBocksteinTarget_page_eq_zero_of_boundary` 已给出最后一个纯页面步骤：
一旦环境代表落入该入射边界子对象，靶页面类即为零。

## 当前唯一工作路线

当前只构造 Adams 谱序列到 λ-Bockstein 谱序列的态射。起点是已经得到的
E₂ 页比较。对每一页，Adams 微分与由边界 ESS 定义的 λ-Bockstein 微分相容；
因此页面映射保持循环子群 `Zᵢ`，也保持边界子群 `Bᵢ`。对相应商取诱导映射，
得到下一页页面映射。由此对 `Zᵢ`、`Bᵢ` 归纳，构造全部页面的态射。

不得转向其他比较问题、额外提升问题或任何不服务于这条归纳的论证。后续
修改只能补足：E₂ 起始映射、微分相容性、`Zᵢ` 与 `Bᵢ` 的归纳、以及商上的
下一页映射。

### `Zᵢ`、`Bᵢ` 归纳的严格步骤

设第 `i` 页的比较映射已经给出，且与第 `i` 页微分交换。若一个页面类的
微分为零，其像的微分也为零，因此映射限制为循环子群之间的映射。若一个
页面类是某个微分的值，其像仍是对应微分的值，因此映射把边界子群送入边界
子群。于是它给出

```text
ker(d_i^Adams) / im(d_i^Adams)
  → ker(d_i^Bockstein) / im(d_i^Bockstein).
```

两边分别经谱序列定义中的规范同构识别为下一页的
`Z_(i+1) / B_(i+1)`。这定义第 `i+1` 页的比较映射。现有
`SpectralSequence.pageHomologyIso` 正是这两个规范同构的 Lean 实现，
`affineReindexedPageEquivSucc` 已将此步骤接入比较文件。

对新得到的页面映射，已证的“Adams 微分对应边界 ESS 微分”公式给出第
`i+1` 页的微分交换式。故可重复上述核、像、商的构造。以 E₂ 页比较为基例，
归纳产生所有页面映射及其微分相容性，正好组成
`CanonicalAdamsToLambdaBocksteinMorphism`。

**后续纠正：** 下文记录的 Lean 接口现状仍需区分，但把这些缺口直接
当成数学证明的停止理由不正确。正确主线是从自由 λ 模 E₂ 出发，
用自然性计算全部有限 λ 商的 Adams，再追踪 E∞ 和余纤维映射以计算
边缘 ESS。详细逐页归纳见 [有限 λ 商的证明](LambdaQuotientProof.md)。

## 本轮完成的证明

1. 从已有的有限 λ-商 E₂ 支撑结论，推出其 Adams 谱序列在
   `max 2 (n+1)` 页退化：`synAdams_mod_lambda_degenerates`。
2. 对第一次 λ-商，证明 E₂ 只支撑在内部次数等于权重的对角线上，
   并因此从 E₂ 退化：`synAdams_mod_lambda_one_e2_diagonal`、
   `synAdams_mod_lambda_one_degenerates`。
3. 构造该商对象所有后续有限页、极限页、收敛关联分次与其 E₂ 的同构：
   `synAdams_mod_lambda_one_pageIso`、
   `synAdams_mod_lambda_one_eInftyIso`、
   `synAdams_mod_lambda_one_associatedGradedIso`。
   消失性和退化性均已由已有商支撑结论推出，没有另列为假设。
4. 对无界 ESS 的实际页对象，证明第零页源项等于源关联分次，并通过收敛
   同构将其识别为源 Adams 极限页：
   `SyntheticExtensionCoreData.e0SourceIsoAssociatedGraded`、
   `SyntheticExtensionCoreData.e0SourceIso`。
   证明使用原来的无界 ESS、它与未截断复形的页同构，以及二项复形源列
   没有入射微分这一事实；没有使用 bounded ESS。
5. 将上述同构复合，得到 `lambdaBocksteinESSSourceE0Iso`：
   λ 边缘 ESS 的实际第零页源项，同构于 `νX/λ` 的 Adams E₂ 项。

第 5 项只比较源列与商对象的 E₂。它不是整个 ESS 与 `νX` 的 Adams
谱序列的同构，也没有把 ESS 第零页改名为 Adams 第二页。

## 为什么还不能完成微分比较

### 收敛对象没有被识别为真实同伦群

`Adams.lean` 的 `synAdamsConvergence` 返回某个分次阿贝尔群、某个滤过及
极限页同构。其类型没有把这些群识别为球到对象的态射群，也没有把该滤过
识别为同一文件中的 `synAdamsFiltration`。

`SyntheticExtensionCoreData` 同样允许抽象收敛对象。它的 `eMap_eq`
固定的是极限页映射。结合收敛相容性，可获得关联分次上的相容方块；
类型中没有说明 `convergenceMap.aMap` 等于实际同伦映射。

因此，`LambdaBoundary.lean` 中已经证明的 λ 边缘自然性与正合性，
作用于实际的表示同伦群；ESS 的滤过循环和微分则来自
`convergenceMap.aMap`。两者目前没有可用于 Lean 改写的连接。

### 关联分次映射不足以恢复高阶 ESS 微分

这个区别有具体数学内容。例如自由阿贝尔群的两个生成元分别放在滤过
零层和一层，二层为零。考虑两个保滤过映射：零映射，以及将零层生成元
送到一层生成元、将一层生成元送到零的映射。

两者诱导的关联分次映射都是零，但其二项滤过复形的第一微分不同：
前者为零，后者在相应两个分量之间是同构。因此，单凭 `eMap_eq` 和
关联分次上的同构，不能确定 ESS 的后续微分。

这个例子说明缺失连接的作用；它不声称论文中的 λ-Bockstein 比较是错的。

### Adams 页上的 λ 作用也缺少连接

`synAdamsSS_functorial` 的类型给每个映射指定一个谱序列态射，但现有接口
没有声明其保持复合、恒等映射，也没有提供与同伦群收敛映射相容的函子。
因此不能仅由它的名字，把合成相等的自然性方块直接送到 Adams 页上。

`synAdamsSS_zlambda_module` 现已改为真正的分次 λ 作用：λ 从权重 `w`
映到 `w-1`，并且类型中包含它与每页微分交换的等式。此前给每个固定
三次数单独指定 `Polynomial ℤ` 模结构的声明不能表达降权重，已经删除。

## 完成最终比较的主线（纠正）

先计算自由 λ 模除以 λⁿ 的 E₂，再同时归纳商的页对象与商映射。
在微分目标仍处于商支撑带内时，源的商映射为同构、目标的商映射为
单射，自然性便确定微分；越出支撑带的微分由消失性确定。
由此计算 E∞，并保留 λ、商限制和余纤维图中的映射，最后计算边缘 ESS。

上面的任意保滤过映射例子没有这些 λ 结构，只能说明不能丢掉结构，
不能作为拒绝这条路线的依据。此前要求先重建完整 Adams 构造的结论撤回。
仍然禁止通过新公理、证明占位或额外比较假设来代替这些证明。

## 验证

- 基线：`lake build KIPBase.Synthetic.Rigidity KIPBase.Synthetic.AdamsVanishing
  KIPBase.Synthetic.ExtensionSS` 通过，3186 jobs。
- 新增商退化和比较：`lake build KIPBase.Synthetic.Rigidity` 通过，3176 jobs。
- 新增实际 ESS 源项比较：`lake build KIPBase.Synthetic.ExtensionSS` 通过，3186 jobs。
- 全量 `lake build` 通过，3213 jobs；日志：
  `.lake/lambda-comparison-full-build.log`。
- 九个新增公开声明的 `#print axioms` 审计通过，无 `sorryAx`，只依赖
  Lean 基础公理和项目既有公理；日志：`.lake/lambda-comparison-axioms.log`。
