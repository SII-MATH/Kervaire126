module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Iteration.Equivalence.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual loop-to-iterated-fiber comparison is strictly natural for
every strictly commuting square of prespectrum maps. -/
theorem fiberIterationComparison_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    fiberIterationComparison f ≫
      fiberMap (fiberProjection f) (fiberProjection g) (fiberMap f g a b h) a
        (fiberMap_projection f g a b h).symm =
      loopMap b ≫ fiberIterationComparison g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext (a.point n) rfl
  · apply ContinuousMap.ext
    intro s
    exact a.point n

end KIP126.StableHomotopy.Implementation.Prespectrum
