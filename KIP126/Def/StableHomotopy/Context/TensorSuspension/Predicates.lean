import KIP126.Def.StableHomotopy.Context.Data

namespace KIP126.StableHomotopy

open CategoryTheory MonoidalCategory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [∀ X : C, (tensorRight X).CommShift ℤ]

/-- Compatibility of the given right-tensor suspension comparisons with
maps in the right variable and with reassociation, at suspension one.
These are properties of the ambient tensor and shift structures, not
assumptions about Adams pages, differentials, or a coefficient ring.
Individual `CommShift` instances do not supply these family compatibilities. -/
structure RightTensorSuspensionCompatibility : Prop where
  natural_right : ∀ (B : C) {X Y : C} (f : X ⟶ Y),
    (B⟦(1 : ℤ)⟧ ◁ f) ≫ (Functor.commShiftIso (tensorRight Y) (1 : ℤ)).hom.app B =
      (Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app B ≫ (B ◁ f)⟦(1 : ℤ)⟧'
  associator : ∀ (B X Y : C),
    (α_ (B⟦(1 : ℤ)⟧) X Y).hom ≫
        (Functor.commShiftIso (tensorRight (X ⊗ Y)) (1 : ℤ)).hom.app B =
      ((Functor.commShiftIso (tensorRight X) (1 : ℤ)).hom.app B ▷ Y) ≫
        (Functor.commShiftIso (tensorRight Y) (1 : ℤ)).hom.app (B ⊗ X) ≫
        (α_ B X Y).hom⟦(1 : ℤ)⟧'

end KIP126.StableHomotopy
