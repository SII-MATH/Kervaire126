import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
import KIP126.Def.Kervaire.Route.Extensions.Stretching.Predicates

/-! 本文待证工具；所有对象、代表和扩张均从同一个 Route.Model 派生。
这里只定义模型上的性质；定义该命题不把它作为 M 的字段或 A(M) 的输入。
独立的本文证明目标位于 Main/Solution/Tools。 -/
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

/-- 本文待证工具（原 am7）：有限页 relation 的 stretching 交付命题。
参考 MainPaper Proposition `prop:dec738d3` 及 Corollary `cor:dfc6043e`。
本项目要求源、靶都已属于后页所需的 cycle 层，并排除上述含 b=0 的
障碍候选；这是明确的充分条件版本；模型相容条件已有类型，比较输入与证明仍待交付。
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
