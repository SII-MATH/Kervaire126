import KIP126.Def.Synthetic.PageExtension.Crossing.Predicates

/-! M: the actual shorter-extension crossing predicate used by finite stretching.
This defines a condition, not a stretching theorem or an external input. -/
namespace KIP126.Synthetic.PageExtension

open CategoryTheory CategoryTheory.MonoidalCategory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Synthetic.PageExtension KIP126.Classical.Adams.PageRepresentatives

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

/-- 论文有限 stretching：有限 stretching 的较短 extension 障碍候选。
所有标签、essential 性及较大的普通 Adams 边界来自同一个 P。
额外要求较短源不能存活到后页所需的 cycle 层；这不是给定严格代表元
无法提升的充要条件。这里 b 允许为零，故排除这些候选比论文
Corollary `cor:dfc6043e` 印出的 b>0 条件更强。 -/
def FinitePageExtensionNonliftableCrossing (P : NormalizedPageFamily H N F f)
    (rEarlier rLater : ℕ) (n s t : ℤ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ a ≤ rEarlier - 2 ∧
    (b : ℤ) ≤ n - a - normalizedExponent H f ∧
    ∃ (x' : Ambient H X (s + a, t + a))
      (y' : Ambient H Y (s + a + (n - a - b), t + a + (n - a - b))),
      x' ∉ cycles H X ((rLater : ℤ) - 1 - a) (s + a, t + a) ∧
      ∃ W' : FiniteExtensionWitness P (rEarlier - a) (n - a - b)
          (s + a) (t + a) x' y',
        W'.Essential ∧ y' ∉ boundaries H Y
          (1 + n - b - normalizedExponent H f)
          (s + a + (n - a - b), t + a + (n - a - b))

end KIP126.Synthetic.PageExtension
