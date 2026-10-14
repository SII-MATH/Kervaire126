/-
  KIPBase.StableHomotopy.Category
  The abstract stable homotopy category interface and its optional enhancement.
-/
import KIPBase.Mathlib
import KIPBase.StableHomotopy.TensorTriangulatedCategory

open CategoryTheory MonoidalCategory Pretriangulated

namespace KIPBase.StableHomotopy

universe u v

/-- An abstract stable homotopy category: a pretriangulated category with an
integer shift and a monoidal structure. Model-specific properties are kept in
`StableHomotopyCategoryEnhancement`. -/
class StableHomotopyCategory (𝒮 : Type u) extends
    Category.{v} 𝒮,
    Preadditive 𝒮,
    HasShift 𝒮 ℤ,
    MonoidalCategory 𝒮 where
  /-- Every shift functor is additive. -/
  shiftAdditive : ∀ (n : ℤ), (shiftFunctor 𝒮 n).Additive
  /-- The category has a zero object. -/
  hasZeroObject : Limits.HasZeroObject 𝒮
  /-- The category is pretriangulated. -/
  pretriangulated : Pretriangulated 𝒮

attribute [instance] StableHomotopyCategory.shiftAdditive
attribute [instance] StableHomotopyCategory.hasZeroObject
attribute [instance] StableHomotopyCategory.pretriangulated

/-- Additional tensor and cofiber structure used by the stable homotopy
development. The concrete spectrum category receives this enhancement from its
chosen model realization; abstract stable homotopy categories must provide it
explicitly. -/
class StableHomotopyCategoryEnhancement (𝒮 : Type u)
    [StableHomotopyCategory.{u, v} 𝒮] where
  /-- Closed symmetric tensor triangulated structure. -/
  closedSymmetricTensorTriangulated : ClosedSymmetricTensorTriangulated 𝒮
  /-- Tensor-compatible functorial cofiber structure. -/
  tensorTriangulatedFunctorialCofiber : TensorTriangulatedCatWithFunctorialCofiber 𝒮

attribute [instance] StableHomotopyCategoryEnhancement.closedSymmetricTensorTriangulated
attribute [instance] StableHomotopyCategoryEnhancement.tensorTriangulatedFunctorialCofiber

end KIPBase.StableHomotopy
