module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The original reduced cylinder of the identity is an actual strict
functor, using the existing mapping-cylinder maps. -/
noncomputable def cylinderFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj X := mappingCylinder (𝟙 X)
  map f := mappingCylinderMap (𝟙 _) (𝟙 _) f f (by simp)
  map_id X := mappingCylinderMap_id (𝟙 X) (by simp)
  map_comp f g := (mappingCylinderMap_comp (𝟙 _) (𝟙 _) (𝟙 _)
    f f g g (by simp) (by simp) (by simp)).symm

/-- Restrict a map on the original cylinder to its retained path. -/
noncomputable def cylinderPathCurry {X Y : Prespectrum.{u}}
    (f : cylinderFunctor.obj X ⟶ Y) : X ⟶ pathPrespectrum Y :=
  mappingCylinderPath (𝟙 X) ≫ pathMap f

/-- A strict path-valued map descends to the original cylinder, with
its last value on the attached target summand. -/
noncomputable def cylinderPathUncurry {X Y : Prespectrum.{u}}
    (f : X ⟶ pathPrespectrum Y) : cylinderFunctor.obj X ⟶ Y :=
  mappingCylinderDesc (𝟙 X) (f ≫ pathEvaluation Y 1) f (by simp)

end KIP126.StableHomotopy.Implementation.Prespectrum
