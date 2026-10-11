module

public import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
public import KIP126.Def.Kervaire.Route.Extensions.Stretching.Predicates

@[expose] public section

/-! 本文待证工具；所有对象、代表和扩张均从同一个 Route.Model 派生。
这里只定义模型上的性质；定义该命题不把它作为 M 的字段或 A(M) 的输入。
可复用证明和显式剩余义务位于同目录 Proofs.lean；文献输入的构造留在 Interface。 -/
namespace KIP126.Kervaire.Route.Tools

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Kervaire.Route KIP126.Classical.Adams KIP126.Classical.Adams.PageRepresentatives

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {M : MilnorCooperations H}
  (D : Model H M Syn)

/-- 本文待证工具（原 am7）：保留 λ 层数的有限页 stretching 充分条件。
参考 MainPaper Proposition `prop:dec738d3` 中同一有限商内的修正过程。
源、靶须属于后页所需的 cycle 层；排除的障碍是在早页同一个有限商中，
源不属于后页 ρ 的 E∞ 像、目标非零的实际较短扩张（包括非 essential 的扩张）。
不能改为只排除较小商中的无层扩张：乘 λ 可能杀掉低滤过项。
这比只排除 essential crossings 更强，不声称等价于原跨页候选或印出的推论。
有限滤过修正已在同目录 Proofs.lean 给出；其模型比较前提和传递依赖仍须核验。
结论只给出后页 extension 的存在，不声称任意指定的早期严格解可提升，
也不蕴含相容解塔或未截断 extension 的存在。 -/
def FinitePageExtensionStretchingLaw (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (rEarlier rLater : ℕ) (n s t : ℤ)
    (x : Ambient H (X.obj D.auxiliary) (s, t)) (y : Ambient H (Y.obj D.auxiliary) (s + n, t + n)),
    2 ≤ rEarlier → rEarlier ≤ rLater →
    (normalizedExponent H f : ℤ) ≤ n →
    n ≤ (rEarlier : ℤ) - 2 + normalizedExponent H f →
    IsCycle H (X.obj D.auxiliary) ((rLater : ℤ) - 1) (s, t) x →
    IsCycle H (Y.obj D.auxiliary) ((rLater : ℤ) - 1 - n + normalizedExponent H f) (s + n, t + n) y →
    FiniteExtension D X Y f rEarlier n s t x y →
    ¬ FiniteExtensionNonliftableCrossing D X Y f rEarlier rLater n s t →
    FiniteExtension D X Y f rLater n s t x y

end KIP126.Kervaire.Route.Tools
