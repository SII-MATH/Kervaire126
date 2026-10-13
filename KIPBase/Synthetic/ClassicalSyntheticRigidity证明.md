# 从 E₂ 比较与 λ 反演比较证明 Adams 微分对应

本证明按用户指定的顺序进行：E₂ 页的关系 → 反演 λ 后的谱序列比较 → 反演前的微分公式。这里只使用下面两项比较事实；不使用 rigidity_free_lambda_pages 或其中的 differential_compat。

## 输入与结论

记经典 Adams 谱序列为 \(C_r^{s,t}\)，记 \(\nu X\) 的 synthetic Adams 谱序列为 \(S_r^{s,t,w}\)。采用项目中的 AIM 指标：

\[
d_r:S_r^{s,t,w}\longrightarrow S_r^{s+r,t+r-1,w},
\qquad |\lambda|=(0,0,-1).
\]

第一项输入是保持实际 λ 作用的 E₂ 比较

\[
S_2\cong C_2\otimes\mathbb F_2[\lambda],
\]

其中经典双次数 \((s,t)\) 的生成元位于权重 \(t\)。第二项输入是实际 λ 反演诱导的谱序列比较：反演后的 synthetic Adams 谱序列与经典 Adams 谱序列的 Laurent 扩张等价，并且在 E₂ 页上与第一项比较的反演一致。这项输入包括微分及同调到下一页的相容性，不能仅以两个反演后页面对象同构代替。

固定一个权重，在 Laurent 扩张中除去该权重的 λ 单项式，得到反演比较映射

\[
q_r^{s,t,w}:S_r^{s,t,w}\longrightarrow C_r^{s,t}.
\]

它满足

\[
q_r(\lambda z)=q_r(z),\qquad
q_r(d_r^{\mathrm{syn}}z)=d_r^{\mathrm{cl}}q_r(z),
\]

并在下一页上诱导同调映射。这里的微分相容来自反演后的谱序列比较，不是待证的反演前 rigidity。

要证明：对每个 \(r\ge2\) 和经典微分 \(d_r^{\mathrm{cl}}x=y\)，选取分别位于顶权重 \(t\)、\(t+r-1\) 的 synthetic 提升 \(\widetilde x,\widetilde y\)，有

\[
d_r^{\mathrm{syn}}\widetilde x
=\lambda^{r-1}\widetilde y.
\]

这些提升存在；右边作为微分目标与提升的选择无关。公式包含零微分，并且其他权重的微分由 λ 线性得到。

## 先由 E₂ 归纳证明反演映射的单射范围

令 \(a=t-w\) 为 λ 深度。对每个 \(r\ge2\)，同时证明：

1. 若 \(a<0\)，则 \(S_r^{s,t,w}=0\)。
2. 若 \(a\ge0\)，则 \(q_r^{s,t,w}\) 满射。
3. 若 \(a\ge r-2\)，则 \(q_r^{s,t,w}\) 为同构。

在第二页，这三项直接来自自由 λ 模的 E₂ 比较，且 \(q_2\) 是该比较给出的实际映射。

假设三项在第 \(r\) 页成立。对非零的可能源，\(a\ge0\)。它的微分目标为 \((s+r,t+r-1,w)\)，其深度为

\[
a+r-1\ge r-1\ge r-2.
\]

因此目标处的 \(q_r\) 单射。结合反演比较的微分相容，得到

\[
d_r^{\mathrm{syn}}z=0
\quad\Longleftrightarrow\quad
d_r^{\mathrm{cl}}q_r(z)=0.
\]

若一个经典第 \(r\) 页类是循环，源处 \(q_r\) 的满射给出它的 synthetic 提升；上述等价说明这个提升也是循环。因此 \(q_r\) 在循环上满射，继而在第 \(r+1\) 页的同调上满射。这证明第二项的归纳步骤。第一项则由零群的后续页仍为零得到。

再设中心分量的深度 \(a\ge r-1\)。中心处 \(q_r\) 已经是同构，出微分目标处 \(q_r\) 单射，故两边的循环由中心处同构精确识别。入微分的源为

\[
(s-r,t-r+1,w),
\]

其深度为 \(a-(r-1)\ge0\)，所以该源处 \(q_r\) 满射。微分相容于是说明：中心处同构把 synthetic 入边界精确映为经典入边界。对循环除以入边界，得到 \(q_{r+1}\) 为同构。其范围正是

\[
a\ge r-1=(r+1)-2.
\]

归纳完成。特别地，可能的微分目标处，反演比较映射总是单射。这一结论是从 E₂ 比较及逐页同调归纳证明的，没有预先假设后续页自由性或 rigidity 微分公式。

## 还原反演后的微分等式

现在给定 \(d_r^{\mathrm{cl}}x=y\)。顶权重处的 \(q_r\) 满射，故可取

\[
\widetilde x\in S_r^{s,t,t},\quad q_r(\widetilde x)=x,
\qquad
\widetilde y\in S_r^{s+r,t+r-1,t+r-1},\quad q_r(\widetilde y)=y.
\]

反演比较的微分相容给出

\[
q_r(d_r^{\mathrm{syn}}\widetilde x)=y.
\]

实际 λ 作用在反演比较下变为恒等，因此

\[
q_r(\lambda^{r-1}\widetilde y)=y.
\]

这两个元素同在 \(S_r^{s+r,t+r-1,t}\) 中。该分量的深度为 \(r-1\)，故前面证明的 \(q_r\) 单射适用，得到

\[
\boxed{d_r^{\mathrm{syn}}\widetilde x
=\lambda^{r-1}\widetilde y.}
\]

λ 的指数由权重唯一确定：源与 synthetic 微分目标的权重都是 \(t\)，而经典目标的顶权重为 \(t+r-1\)，所以必须乘 \(\lambda^{r-1}\)。

更一般地，对任意 \(a\ge0\) 和 \(z\in S_r^{s,t,t-a}\)，令 \(x=q_r(z)\)，并取上述顶权重提升。反演比较把 \(z\) 与 \(\lambda^a\widetilde x\) 映到同一个经典类；它们的微分也映到同一个经典目标。目标分量的深度为 \(a+r-1\)，反演比较在那里单射，所以

\[
d_r^{\mathrm{syn}}z
=\lambda^{a+r-1}\widetilde y.
\]

这同时证明公式与提升选择无关、零微分的对应，以及所有 synthetic 微分的确定性。非零性也由目标处单射得出：上述 synthetic 微分非零，当且仅当 \(y\ne0\)。

## 与当前 Lean 源码的关系

数学证明已写出。参考的本地原文是 Source/BHS/source/SynRevAdams.tex 中反演映射及 thm:synth-ASS 的归纳证明（第 70–96 行）；本文件展开了其中目标无 λ 挠元的归纳步骤，并使用项目的 AIM 权重。

这还不是编译通过的 Lean 替代证明。当前 KIPBase 中没有独立实现上述实际 λ 反演谱序列比较及其与 E₂ 比较、下一页同调的相容；现有 Rigidity.lean 的翻译定理使用 rigidity_free_lambda_pages.differential_compat，因此不能充当本证明的形式化实现。这里没有新增公理，也没有把未完成的形式化工作标为完成。
