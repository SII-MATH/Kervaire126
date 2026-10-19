module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Adjunction.Hom.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem cylinderPathCurry_uncurry {X Y : Prespectrum.{u}}
    (f : X ⟶ pathPrespectrum Y) : cylinderPathCurry (cylinderPathUncurry f) = f := rfl

@[simp] theorem cylinderPathCurry_zero {X Y : Prespectrum.{u}}
    (f : cylinderFunctor.obj X ⟶ Y) :
    cylinderPathCurry f ≫ pathEvaluation Y 0 = mappingCylinderInclusion (𝟙 X) ≫ f := rfl

@[simp] theorem cylinderPathCurry_one {X Y : Prespectrum.{u}}
    (f : cylinderFunctor.obj X ⟶ Y) :
    cylinderPathCurry f ≫ pathEvaluation Y 1 = mappingCylinderSection (𝟙 X) ≫ f := by
  change (mappingCylinderPath (𝟙 X) ≫ pathMap f) ≫ pathEvaluation Y 1 = _
  rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_one,Category.id_comp]

theorem cylinderPathCurry_natural_left {X X' Y : Prespectrum.{u}}
    (f : X' ⟶ X) (g : cylinderFunctor.obj X ⟶ Y) :
    cylinderPathCurry (cylinderFunctor.map f ≫ g) = f ≫ cylinderPathCurry g := rfl

@[simp] theorem cylinderPathUncurry_curry {X Y : Prespectrum.{u}}
    (f : cylinderFunctor.obj X ⟶ Y) : cylinderPathUncurry (cylinderPathCurry f) = f := by
  apply mappingCylinderHom_ext (𝟙 X)
  · change mappingCylinderSection (𝟙 X) ≫
      mappingCylinderDesc (𝟙 X) _ _ _ = _
    rw [mappingCylinderSection_desc]
    change (mappingCylinderPath (𝟙 X) ≫ pathMap f) ≫ pathEvaluation Y 1 = _
    rw [Category.assoc,pathMap_evaluation,← Category.assoc,mappingCylinderPath_one,
      Category.id_comp]
  · rfl

theorem cylinderPathUncurry_natural_left {X X' Y : Prespectrum.{u}}
    (f : X' ⟶ X) (g : X ⟶ pathPrespectrum Y) :
    cylinderPathUncurry (f ≫ g) = cylinderFunctor.map f ≫ cylinderPathUncurry g := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  obtain ⟨q,rfl⟩ := mappingCylinderMk_surjective (𝟙 X') n z
  cases q <;> rfl

theorem cylinderPathCurry_natural_right {X Y Y' : Prespectrum.{u}}
    (f : cylinderFunctor.obj X ⟶ Y) (g : Y ⟶ Y') :
    cylinderPathCurry (f ≫ g) = cylinderPathCurry f ≫ pathFunctor.map g := by
  change mappingCylinderPath (𝟙 X) ≫ pathMap (f ≫ g) = _
  rw [pathMap_comp,← Category.assoc]
  rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
