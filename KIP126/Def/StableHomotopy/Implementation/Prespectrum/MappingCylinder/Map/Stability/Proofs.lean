module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Map.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The original mapping-cylinder map is a stable equivalence whenever
its target map is, by the actual deformation-retract projections. -/
theorem mappingCylinderMap_stableEquivalence {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (hb : stableEquivalences b) :
    stableEquivalences (mappingCylinderMap f g a b h) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  letI := stableEquivalences.Q_inverts _ hb
  letI := stableEquivalences.Q_inverts _ (mappingCylinderProjection_stableEquivalence f)
  letI := stableEquivalences.Q_inverts _ (mappingCylinderProjection_stableEquivalence g)
  have e := congrArg sourceLocalization.map (mappingCylinderProjection_natural f g a b h)
  simp only [Functor.map_comp] at e
  exact IsIso.of_isIso_fac_right e

end KIP126.StableHomotopy.Implementation.Prespectrum
