# BHS 适用性：暂停点与待办

2026-10-12 按用户要求收尾暂停。固定球面、Cν、tmf 及其整数平移的 BHS 适用性尚未完成；以下缺口允许暂留 `sorry`。已完成的基础证明保留，具体声明与依赖记录在 Blueprint 和 `external-inputs.json`。

## 已完成到哪里

- 原稳定同伦范畴中的 Moore 完备化、Postnikov 塔和相应极限工具已有实际构造及通用证明。
- 原 doubled-bond 球面与实际 dyadic scalar telescope 的比较已证明同构：`sourceSphereInvertTwoTelescopeComparison_isIso`；scalar telescope 的正交性检测准则也已证明。
- 原 diagonal smash 的稳定同伦群与实际双指标网格已比较；任意原谱的 coproduct、任意附胞族及有限单纯实现加不交基点的 smash 稳定性已证明。
- 原球面 self-map 的有限 collapse 求和、显式可逆仿射 self-map 的 ±generator 公式、实际细分顶点的仿射无关性及 full-star 分片坐标已证明。
- Moore 完备化的 HF₂ 局部性及其与给定反射的比较，仍明确以 `IsIso sourceModTwoMooreHeartToHF2` 为条件。这一条件尚未证明。
- BHS 源定理已有单独的条件声明并保留 `sorry`。其运输证明不代替固定对象的适用性证明。

## 待办

1. **接通原完备性谓词。** 从 `Prespectrum.IsTwoComplete` 的两组自然数平移出发，用 `source_shiftFunctor_obj` 和已证 doubled-bond/telescope 同构，得到 telescope 所有整数平移的正交性；再接 `sourceIsScalarComplete_iff_scalarSphereTelescope_orthogonal` 与 Moore 单位的普遍性质。入口：[telescope 比较](../KIP126/Def/StableHomotopy/Implementation/Sphere/InvertTwo/Telescope/Equivalence/Proofs.lean)、[scalar 检测](../KIP126/Def/StableHomotopy/Implementation/Prespectrum/ScalarLocalization/Detection/Proofs.lean)。

2. **完成实际球面的模二核。** 为 `independentSpanAffineEquiv` 补 sum-one 重心公式和有限维同胚 API；用实际 full-star 顶点、分片和坐标，比较原局部 complement-collapse 与显式 affine sphere self-map。随后由有限求和证明局部贡献、`ker(π₀S → 𝔽₂) = 2π₀S`，进而证明 `sourceModTwoMooreHeartToHF2` 是同构。已有的 ±generator 公式只适用于显式仿射映射，尚未适用于每个实际 collapse 分支。入口：[仿射 span](../KIP126/Def/Topology/Simplex/AffineSpan/Proofs.lean)、[分片](../KIP126/Def/Topology/SimplicialRealization/OrderComplex/Degree/Sheets/Proofs.lean)、[Moore heart 比较](../KIP126/Def/StableHomotopy/Implementation/HF2/Moore/Postnikov/Proofs.lean)。

3. **完成无限 CW 参数的稳定性。** 任意附胞族已处理，仍缺无限 sequential colimit 对任意原输入谱的比较，以及所需的基点识别。需要实际相对同伦有限子复形支撑或相应同伦余极限论证；raw wedge 的同伦有限支撑本身尚不足以完成这一步。最终填入原 `diagonalSmash_stable_right`。入口：[任意附胞族](../KIP126/Def/StableHomotopy/Implementation/Prespectrum/Smash/Space/Parameter/Cells/General/Proofs.lean)、[Smash](../KIP126/Def/StableHomotopy/Implementation/Smash.lean)。

4. **完成固定 HF₂ 反射与基础模型。** 构造全局 `completionModel_exists`，证明所需单位比较，接回 `completedSphereMooreUniversal` 和固定 `implementation_exists`。已有给定反射下的比较不证明反射存在。入口：[Completion](../KIP126/Def/StableHomotopy/Implementation/Completion.lean)、[固定 Implementation](../KIP126/Def/Solution/Implementation.lean)。

5. **构造并识别固定 tmf 和路线。** 补实际 tmf 对象、单位、连通性、mod-two 同调识别与有限型证明；给出与所选 detector 的保单位比较，完成 `StandardRoute` 与背景。抽象多项式分次有限性尚未识别实际 tmf。Cν 的结论须使用同一实际 ν 映射的余纤维。入口：[StandardRoute](../KIP126/Def/Solution/StandardRoute.lean)、[背景](../KIP126/Def/Solution/StandardRouteBackground.lean)、[文献交付](../KIP126/Interface/Solution/Literature/Delivery.lean)。

6. **证明实际 Adams 幂零完备和强收敛。** 补实际 Adams residual 塔的所需无环性、层有限性和乘积比较，将已证通用极限/滤过工具应用于固定对象。Moore 完备性还不是这两个结论。同步 develop 后，`standardSphereApplicability` 已有组装证明；仍须补其依赖的实际塔连通性和 Moore 对象 Postnikov 层两处未完成证明，并证明 Cν、tmf 及全部整数平移的适用性。入口：[固定球面适用性](../KIP126/Def/StageInput/StandardSphere/Sequence/Proofs.lean)、[Adams 滤过完备性工具](../KIP126/Def/ClassicalAdams/Convergence/Tower/Completion/Proofs.lean)。

7. **完成 BHS 特化交付。** 在实际模型及其对应识别完成后，逐条核验源声明与 BHS 原文的对象、假设、次数、量词和结论；然后用恒等比较直接给出固定对象的未截断提升、λ 整除及四项 realization 结论。BHS 源定理本身可保留 `sorry`，适用性与比较的待办仍须独立追踪。入口：[BHS 源声明与运输](../KIP126/Interface/Solution/Literature/Route/BHS.lean)。

继续工作时先从第 1 项接通已有比较；第 2、3、5 项可分别推进。每次改变公共声明或证明依赖，同步 Blueprint、源清单并检查公理依赖。

## 收尾验证

完整 `lake build KIP126`（6634 jobs）、`scripts/check.sh`、`leanblueprint web`、Blueprint 声明检查、源清单生成及其 Lean 检查、`git diff --check` 均通过。上述通过状态允许项目中已有的未完成证明；本目标仍处于暂停、未完成状态。
