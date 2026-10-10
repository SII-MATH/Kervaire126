import KIP126.Def.StableHomotopy.Context.TensorSuspension.Predicates

namespace KIP126.StableHomotopy

open CategoryTheory MonoidalCategory BraidedCategory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [BraidedCategory C]
  [∀ X : C, (tensorRight X).CommShift ℤ]
  [∀ X : C, (tensorLeft X).CommShift ℤ]

/-- Compatibility of the supplied left and right tensor suspension
comparisons with the ambient braiding. This is a structural condition,
not an assertion that any Adams tower pairing is symmetric. -/
def TensorSuspensionBraidingCompatibility : Prop :=
  ∀ (X B : C),
    (β_ X (B⟦(1 : ℤ)⟧)).hom ≫
        (Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app B =
      (Functor.commShiftIso (tensorLeft X) (1 : ℤ)).hom.app B ≫
        (β_ X B).hom⟦(1 : ℤ)⟧'

end KIP126.StableHomotopy
