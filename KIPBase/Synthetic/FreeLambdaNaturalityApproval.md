# νX Adams 中 λ 保持 essential differential：接口修正审批报告

**状态：已批准并实现。**

## 要证明的结论

对 `νX` 的 synthetic Adams 谱序列，若 `x`、`y` 是同一页上的类，则

\[
d_r x=y\text{ essential}
\quad\Longleftrightarrow\quad
d_r(\lambda x)=\lambda y\text{ essential}.
\]

λ 将权重降低一，目标次数按交换律作唯一的三次数搬运。

## 已经无公理完成的部分

1. `FreeLambdaE2.lambdaPowIso`：自由分次 λ 模中，只要源、目标都在
   自由塔内，乘 `λ^n` 就是两份生成元之间的同构。
2. `FreeLambdaE2.lambdaPow_injective`：上述 λ 乘法因此单射。
3. `FreeLambdaPageStep.lambda_injective`：任意页面上的自由 λ 步都给出
   实际 λ 映射的单射性。
4. `SynAdamsLambdaModule.pageDifferentialEssential_lambda_iff`：由 Adams
   自然性方块和目标 λ 单射，形式化推出 essential 的双向等价。

这些声明均为定义或定理，没有增加公理。

## 当前接口为什么还不能实例化到 νX

`synAdamsSS_zlambda_module` 目前只给每一页一族 λ 映射以及它与该页
微分交换的等式。它没有说明：

- 第二页与自由 λ 模的同构保持实际 λ 映射；
- 后一页的 λ 映射是前一页 λ 映射在同调上诱导的映射。

因此当前类型允许把所有页面上的 λ 映射都取成零；零映射仍满足
`comm_d`。另一方面，`einfty_nuX_mod_lambda` 只给页面对象的抽象加法群
等价，没有说明该等价保持 λ。故 Lean 中不能从这些现有字段推出实际
λ 映射单射。

## 已批准的原接口修正

没有增加独立的结论公理。实现采用了以下最小修正：

1. 将现有但数学陈述错误的 `rigidity_neg_weight_vanishing` 输入替换为
   `rigidity_free_lambda_pages`。它在 `r-2≤t-w` 的自由范围把相邻权重
   识别为同一生成元，并要求这些同构保持实际 λ 映射。公理声明总数
   没有增加。
2. 从这些自由模同构构造 `FreeLambdaPageStep`，再证明实际 λ 映射单射；
   “单射”本身不是输入字段。
3. 若 `d_r x=y` 可能 essential，则源非零强制 `w≤t`，而目标满足
   `r-2≤(t+r-1)-w`，所以目标处有上述自由 λ 步。最后应用 Adams
   自然性定理。

实现没有把“目标 λ 单射”或最终 essential 等价直接写成公理。
原来数学上错误的 `rigidity_neg_weight_vanishing` 已删除，替换为
`rigidity_free_lambda_pages` 所携带的自由页面同构及 λ 相容方块；单射和
最终等价均为从这些数据推出的定理。
