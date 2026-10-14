module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Equivalence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u

variable {A B : Prespectrum.{u}} (p : A ⟶ B)
  (L : fiber p ⟶ pathPrespectrum A)
  (hp : ∀ s : unitInterval, L ≫ pathEvaluation A s ≫ p = fiberNullPath p ≫ pathEvaluation B s)
  (hzero : L ≫ pathEvaluation A 0 = fiberProjection p)

include L hp hzero

/-- An actual universal lift proves that the constant-path fiber comparison
is a stable equivalence. No regularity condition on that lift is required. -/
theorem strictFiberInclusion_stableEquivalence : stableEquivalences (strictFiberInclusion p) := by
  apply (stableEquivalence_iff_source_isIso (strictFiberInclusion p)).mpr
  exact (inferInstance : IsIso (sourceStrictFiberIso p L hp hzero).hom)

/-- The endpoint of the actual universal lift is the inverse stable equivalence. -/
theorem strictFiberRetraction_stableEquivalence : stableEquivalences (strictFiberRetraction p L hp) := by
  apply (stableEquivalence_iff_source_isIso (strictFiberRetraction p L hp)).mpr
  exact (inferInstance : IsIso (sourceStrictFiberIso p L hp hzero).inv)

end KIP126.StableHomotopy.Implementation.Prespectrum
