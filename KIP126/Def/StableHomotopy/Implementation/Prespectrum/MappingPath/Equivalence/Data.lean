module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The strict mapping-path deformation gives the specified source isomorphism
with the constant-path inclusion and the original source retraction. -/
noncomputable def sourceMappingPathIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.obj X ≅ sourceLocalization.obj (mappingPath f) where
  hom := sourceLocalization.map (mappingPathInclusion f)
  inv := sourceLocalization.map (mappingPathRetraction f)
  hom_inv_id := by
    rw [← Functor.map_comp,mappingPathInclusion_retraction]
    exact sourceLocalization.map_id _
  inv_hom_id := source_mappingPathRetraction_inclusion f

end KIP126.StableHomotopy.Implementation.Prespectrum
