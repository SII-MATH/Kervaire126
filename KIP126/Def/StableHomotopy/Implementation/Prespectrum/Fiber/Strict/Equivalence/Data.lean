module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u

/-- The actual universal lift and its two strict homotopies identify the
strict and path fibers in the specified ordinary stable localization. -/
noncomputable def sourceStrictFiberIso {A B : Prespectrum.{u}} (p : A ⟶ B)
    (L : fiber p ⟶ pathPrespectrum A)
    (hp : ∀ s : unitInterval, L ≫ pathEvaluation A s ≫ p = fiberNullPath p ≫ pathEvaluation B s)
    (hzero : L ≫ pathEvaluation A 0 = fiberProjection p) :
    sourceLocalization.obj (strictFiber p) ≅ sourceLocalization.obj (fiber p) where
  hom := sourceLocalization.map (strictFiberInclusion p)
  inv := sourceLocalization.map (strictFiberRetraction p L hp)
  hom_inv_id := by
    rw [← Functor.map_comp,← strictFiberKernelHomotopy_one p L hp,Functor.map_comp,
      source_pathEvaluation_eq (strictFiber p) 1 0,← Functor.map_comp,
      strictFiberKernelHomotopy_zero p L hp hzero]
    exact sourceLocalization.map_id _
  inv_hom_id := by
    rw [← Functor.map_comp,← strictFiberTailHomotopy_one p L hp,Functor.map_comp,
      source_pathEvaluation_eq (fiber p) 1 0,← Functor.map_comp,
      strictFiberTailHomotopy_zero p L hp hzero]
    exact sourceLocalization.map_id _

end KIP126.StableHomotopy.Implementation.Prespectrum
