module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u

@[simp] theorem strictFiberInclusion_projection {A B : Prespectrum.{u}} (p : A ⟶ B) :
    strictFiberInclusion p ≫ fiberProjection p = pullbackFst p (zeroMap zeroPrespectrum B) := rfl

@[simp] theorem strictFiberRetraction_projection {A B : Prespectrum.{u}} (p : A ⟶ B)
    (L : fiber p ⟶ pathPrespectrum A)
    (hp : ∀ s : unitInterval, L ≫ pathEvaluation A s ≫ p = fiberNullPath p ≫ pathEvaluation B s) :
    strictFiberRetraction p L hp ≫ pullbackFst p (zeroMap zeroPrespectrum B) =
      L ≫ pathEvaluation A 1 := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
