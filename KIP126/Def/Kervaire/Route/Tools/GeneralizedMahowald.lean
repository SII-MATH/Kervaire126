import KIP126.Def.ClassicalAdams.PageRepresentatives.Predicates
import KIP126.Def.Kervaire.Route.Extensions.Crossing.Predicates
import KIP126.Def.ClassicalAdams.Suspension.Predicates
import KIP126.Def.Kervaire.Route.Triangles.Predicates

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

/-- 本文待证工具（原 am7）：MainPaper Theorem 6.12 (`thm:158d451a`) 的实际三角版本。
第二个 no-crossing 分支属于 Z 上的 d_r，在 E_r′ 页检查；不属于 g。
h 的 target 位于 ΣX，其标签通过 D.classicalSuspension 的实际 tower/layer 图和 raw-cycle
商代表元与 x 关联。该比较的构造证明尚未交付，不能以任意 E₂ 等价代替。
结论是存在同余于 y 的真实 f-extension target，模实际 B_r′；不是自由
选取的 fTarget 操作。r′ 及结论页的正性由指数和与三个长度界保证。 -/
def GeneralizedMahowaldLaw (T : TriangleData D.auxiliary) : Prop :=
  ∀ he : (normalizedExponent H T.f : ℤ) + normalizedExponent H T.g +
      normalizedExponent H T.h = 1,
  NormalizedTriangleCompatible D.toModelData T he →
  ∀ (n m l s t : ℤ),
    let r := n + m + l
    let n₁ := n - normalizedExponent H T.f
    let m₁ := m - normalizedExponent H T.g
    let l₁ := l - normalizedExponent H T.h
    let r' := r - m₁
    ∀ (x : Ambient H (T.X.obj D.auxiliary) (s + l, t + l - 1))
      (y : Ambient H (T.Y.obj D.auxiliary) (s + l + n, t + l - 1 + n))
      (xBar : Ambient H (T.Z.obj D.auxiliary) (s, t))
      (yBar : Ambient H (T.Z.obj D.auxiliary) (s + l + n + m, t + l - 1 + n + m))
      (suspendedX : Ambient H ((T.X.obj D.auxiliary)⟦(1 : ℤ)⟧) (s + l, t + l)),
      1 ≤ n₁ → 0 ≤ m₁ → 0 ≤ l₁ →
      IsCycle H (T.X.obj D.auxiliary) n₁ (s + l, t + l - 1) x →
      IsCycle H (T.Y.obj D.auxiliary) (m₁ + 1) (s + l + n, t + l - 1 + n) y →
      IsCycle H (T.Z.obj D.auxiliary) (r - 1) (s, t) xBar →
      IsPermanent H (T.Z.obj D.auxiliary) (s + l + n + m, t + l - 1 + n + m) yBar →
      (D.classicalSuspension T.X).DesuspendsClass (s + l) (t + l) suspendedX x →
      FiniteExtension D T.Z (.shift 1 T.X) T.h r'.toNat l s t xBar suspendedX →
      DifferentialAt H (T.Z.obj D.auxiliary) r (s, t)
        (s + l + n + m, t + l - 1 + n + m) xBar yBar →
      (FiniteExtension.NoCrossing D T.Z (.shift 1 T.X) T.h r'.toNat l s t ∨
        NoCrossingOn H (T.Z.obj D.auxiliary) r r' (s, t)) →
      FiniteExtension D T.Y T.Z T.g (m₁ + 2).toNat m (s + l + n) (t + l - 1 + n) y yBar →
      IsCycle H (T.X.obj D.auxiliary) (n + m + normalizedExponent H T.h) (s + l, t + l - 1) x ∧
        ∃ y' : Ambient H (T.Y.obj D.auxiliary) (s + l + n, t + l - 1 + n),
          FiniteExtension D T.X T.Y T.f (n + m + 1 + normalizedExponent H T.h).toNat
            n (s + l) (t + l - 1) x y' ∧
          Congruent H (T.Y.obj D.auxiliary) r' (s + l + n, t + l - 1 + n) y' y

end KIP126.Kervaire.Route.Tools
