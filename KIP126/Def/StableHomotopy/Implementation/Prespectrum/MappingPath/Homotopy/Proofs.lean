module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingPath.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Path.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

@[simp] theorem mappingPathHomotopy_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathHomotopy f ≫ pathEvaluation (mappingPath f) 0 =
      mappingPathRetraction f ≫ mappingPathInclusion f := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro s
    change z.val.2 (0 * s) = f.level n z.val.1
    rw [zero_mul]
    exact z.property

@[simp] theorem mappingPathHomotopy_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathHomotopy f ≫ pathEvaluation (mappingPath f) 1 = 𝟙 (mappingPath f) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro s
    change z.val.2 (1 * s) = z.val.2 s
    rw [one_mul]

/-- The deformation fixes the constant-path inclusion pointwise. -/
@[simp] theorem mappingPathInclusion_homotopy {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingPathInclusion f ≫ mappingPathHomotopy f =
      mappingPathInclusion f ≫ pathConstant (mappingPath f) := rfl

/-- The actual strict deformation becomes an inverse equation in the specified
ordinary stable localization. -/
theorem source_mappingPathRetraction_inclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    sourceLocalization.map (mappingPathRetraction f) ≫
      sourceLocalization.map (mappingPathInclusion f) = 𝟙 (sourceLocalization.obj (mappingPath f)) := by
  rw [← Functor.map_comp,← mappingPathHomotopy_zero,Functor.map_comp,
    source_pathEvaluation_eq (mappingPath f) 0 1,← Functor.map_comp,
    mappingPathHomotopy_one]
  exact sourceLocalization.map_id _

end KIP126.StableHomotopy.Implementation.Prespectrum
