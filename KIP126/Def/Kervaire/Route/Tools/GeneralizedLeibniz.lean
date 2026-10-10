import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
import KIP126.Def.Kervaire.Route.Extensions.Crossing.Predicates

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

/-- 本文待证工具（原 am7）：MainPaper Theorem 6.1 (`thm:e73f481e`) 的准确交付命题。
所有页面、微分、有限／无限 extension 和 crossing 均来自同一 H、D。
末端次数是 (s+r+l,t+r+l-1)，l-extension 不额外减一次 t。
本定义不声称仅由 M 就能推出此 law；证明使用同一 D 上的文献比较输入及
论文中的 δ／λ／ρ 推理。不要求微分或 extension 非零。 -/
def GeneralizedLeibnizLaw (X Y : ClassicalObject) (f : X.obj D.auxiliary ⟶ Y.obj D.auxiliary) : Prop :=
  ∀ (page : ℕ) (r m l s t : ℤ)
    (x : Ambient H (X.obj D.auxiliary) (s, t)) (y : Ambient H (Y.obj D.auxiliary) (s + m, t + m))
    (xInfinity : Ambient H (X.obj D.auxiliary) (s + r, t + r - 1))
    (yInfinity : Ambient H (Y.obj D.auxiliary) (s + r + l, t + r - 1 + l)),
    2 ≤ page → (page : ℤ) ≤ r →
    (normalizedExponent H f : ℤ) ≤ m →
    m ≤ (page : ℤ) - 2 + normalizedExponent H f →
    (normalizedExponent H f : ℤ) ≤ l →
    IsCycle H (X.obj D.auxiliary) (r - 1) (s, t) x →
    IsCycle H (Y.obj D.auxiliary) (r - 1 - m + normalizedExponent H f) (s + m, t + m) y →
    IsPermanent H (X.obj D.auxiliary) (s + r, t + r - 1) xInfinity →
    IsPermanent H (Y.obj D.auxiliary) (s + r + l, t + r - 1 + l) yInfinity →
    DifferentialAt H (X.obj D.auxiliary) r (s, t) (s + r, t + r - 1) x xInfinity →
    FiniteExtension D X Y f page m s t x y →
    InfiniteExtension D X Y f l (s + r) (t + r - 1) xInfinity yInfinity →
    (NoCrossingOn H (X.obj D.auxiliary) r page (s, t) ∨
      FiniteExtension.NoCrossing D X Y f page m s t) →
    InfiniteExtension.NoCrossing D X Y f l (s + r) (t + r - 1) →
    DifferentialAt H (Y.obj D.auxiliary) (r + l - m) (s + m, t + m)
      (s + r + l, t + r - 1 + l) y yInfinity

end KIP126.Kervaire.Route.Tools
