module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Composition.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem fiberCompositeNullPath_zero {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeNullPath f g ≫ pathEvaluation _ 0 =
      fiberCompositeInclusion f g ≫ fiberCompositeProjection f g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact p.property.1
  · apply ContinuousMap.ext
    intro v
    change g.level n (p.val.2 (Set.Icc.convexComb 0 1 v)) = g.level n (p.val.2 v)
    congr 2
    ext
    simp [Set.Icc.convexComb]

@[simp] theorem fiberCompositeNullPath_one {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    fiberCompositeNullPath f g ≫ pathEvaluation _ 1 = zeroMap _ _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · exact p.property.2
  · apply ContinuousMap.ext
    intro v
    change g.level n (p.val.2 (Set.Icc.convexComb 1 1 v)) = (Z.level n).point
    rw [Set.Icc.convexComb_eq,p.property.2,g.point]

end KIP126.StableHomotopy.Implementation.Prespectrum
