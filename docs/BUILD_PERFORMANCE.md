# 证明文件与增量构建

本轮整理采用仓库固定的 Lean 4.32.2 模块系统，不更换工具链、数学模型或证明状态。
迁移覆盖 `KIP126/` 的生产证明模块和库入口 `KIP126.lean`，包括必要的生成器及
导入解析兼容调整。九个需要读取完整传递证明体的审计文件保留原有格式；
它们没有被生产证明模块导入。`import all` 不具备自动开放全部传递实现的效果，
保留这些审计文件的原环境能够维持原检查强度。

## 文件组织

`Main/Solution/Computation/Route.lean` 保留 `sphere_facts` 的待补证明。
已完成的范围、存活、微分、入射排除及余纤维结论分别位于同名目录下的十个模块。
只需要余纤维与过滤结论的消费者直接导入 `Route.CofiberAndFiltration`。

`Main/Solution/Route/AlphaOne.lean` 保留固定见证上的公共结论，八个通用证明部分
位于 `AlphaOne/`。`Selected.lean` 保留六个公共结论，五个通用证明部分位于
`Selected/`。移动的私有辅助引理仍然私有，跨文件使用处显式声明 `import all`
和 `open private`；这些边会跟踪私有实现的变化。

Section7 的 `Common` 仅保留共享上下文。AlphaOne、Lambda 和 GeneralizedMahowald
的证明由实际使用它们的模块导入，避免所有 Section7 文件都依赖这些证明。

## 模块约定

- 文件以 `module` 开始。`public import` 保持原有声明的传递可见性。
- `@[expose] public section` 保持既有公共定义的可展开性；公共定理的证明不会因此
  成为普通导入所需的公开实现。
- 少数公开定义的实现使用原有私有数据或证明辅助声明。它们使用局部
  `@[no_expose]`，确实需要展开实现的消费者使用 `import all`。原定义体和私有名称保留。
- 不要为了取用一个私有引理而把整个依赖链改成 `import all`。优先导入实际提供
  公共定理的最小模块，新增证明尽量使用现有公共规格。
- 生成 Lean 数据的模块头由对应 Python 生成器同时维护；重新生成后仍须运行
  生成器的检查模式。
- tactic 的实现辅助函数标为 `meta`；`run_cmd` 或 tactic 在编译时执行其他模块的
  代码时，使用准确的 `public meta import`。检查声明的实际证明体或 `thmInfo`
  时，必须能访问声明提供模块的私有产物，不能把公开环境中的表示误判为新增公理。
- `FiniteCertificates` 的 24 个巨大私有字符列表只服务于证明，标为
  `noncomputable` 以省去原生代码生成；原字符数据、定义值和内核计算证明保留。
- 两处长层配对定义局部启用 `backward.proofsInPublic`，避免参数中的算术证明被
  抽成不可见的私有辅助常量。该选项只控制证明抽象，仍经过正常的 Lean 内核检查。
- 长层配对的少数证明文件将参数内的 `(by omega)` 换成同一不等式的显式 `Nat`
  证明项，避免导出类型引用私有辅助常量。新旧完整参数类型通过 `rfl` 相等检查。
- 拆分时必须保留外层 `section`、局部属性和选项的有效范围。例如 AlphaOne 的
  `homogeneousPart` 局部不可展开属性也作用于后面的 Existence 部分及公共结论。
  遗漏这类上下文会使原本较快的证明展开巨大的计算数据。

## 日常验证

在仓库根目录，修改一个文件后先构建相应模块，例如：

```sh
lake build +KIP126.Main.Solution.Route.Section7.ThetaToda
```

提交供审查的结果之前运行完整构建及源码检查：

```sh
lake build
bash scripts/check.sh
```

保留 `.lake/build`。正常的 Lake 构建会检查源码和依赖并复用有效产物，不需要
`lake clean`，也不应使用 `--old` 绕过传递依赖变化。

修改证明所在的模块仍须重新检查。公开产物不变时，普通导入它的下游可以复用缓存；
涉及 `import all`、公开定义体、声明类型、实例、简化规则或导出的公理依赖变化时，
仍可能重建下游。尤其从 `sorry` 改为真实证明可能改变导出的公理依赖信息。
原生代码生成和链接也有各自的依赖，不能把证明缓存复用理解为所有构建任务都跳过。

## 本仓库的验证记录（2026-10-10）

迁移后完整 `lake build` 通过，共 4406 个任务。实际缓存实验在
`Computation/Route/Bounds.lean` 的
`classical_sphere_separated_of_strong_convergence` 原证明前临时加入 `apply id`，
完整构建耗时约 14.8 秒：只重新检查 Bounds 和 5 个读取完整证明的审计模块。
Bounds 的公开 `.olean` 哈希不变、`.olean.private` 哈希改变；Section7、Selected
和最终 `h6_sq_permanent` 的产物及修改时间均未改变。实验随后精确恢复原源码，
再次完整构建通过，耗时约 12.8 秒。这是一次实际证明改动的测量，不保证所有改动
都具有相同缓存边界。

源码检查、生成器检查、Blueprint 网页及声明检查均通过。Main 迁移前后有源码定位的
1834 条声明记录一一对应，声明类别、universes 和传递公理依赖一致。模块系统会
重新提取、命名辅助证明；对由此产生的 36 处类型表示差异和 7 处定义值表示差异，
重建旧表达式后使用 `Lean.Kernel.check` 和 `Lean.Kernel.isDefEq` 检查，全部通过。
其余定义值在已验证的辅助证明名称映射后相同；三个局部记号生成对象单独核对了
模块归属名称变化，原记号源码保留。

模块迁移和成功编译不代表证明完成。Challenge 占位、Solution 的未完成证明、
`sorryAx` 及唯一 `Main.Axiom.challenge2` 继续按原边界审计。
