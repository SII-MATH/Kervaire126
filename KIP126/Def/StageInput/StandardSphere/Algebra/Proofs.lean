import KIP126.Def.StageInput.StandardSphere.Algebra.Data

/-! Canonical inclusions and multiplication in the fixed global E₂ algebra. -/

namespace KIP126.Classical.Adams.Sphere.Internal

open KIP126.Core.Algebra
noncomputable section

attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product

/-- Distinct actual classes of a fixed bidegree remain distinct in the total algebra. -/
theorem embed_injective (p : ℕ × ℕ) : Function.Injective (embed p) :=
  DirectSum.of_injective (β := ActualE2At) p

/-- The total algebra multiplication extends exactly the fixed page product. -/
theorem embed_product (p q : ℕ × ℕ) (x : ActualE2At p) (y : ActualE2At q) :
    embed (p + q) (actualE2Product p q x y) = embed p x * embed q y := by
  exact (DirectSum.of_mul_of x y).symm

/-- The global unit is the inclusion of the actual sphere identity class. -/
theorem embed_unit : embed 0 actualE2Unit = (1 : ActualE2Total) :=
  (DirectSum.one_def ActualE2At).symm

end
end KIP126.Classical.Adams.Sphere.Internal
