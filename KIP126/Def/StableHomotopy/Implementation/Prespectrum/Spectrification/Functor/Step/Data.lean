module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual cylinder step applied to a strict prespectrum map. -/
noncomputable def spectrificationCylinderMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    spectrificationCylinderStep X ⟶ spectrificationCylinderStep Y :=
  mappingCylinderMap (spectrificationStepUnit X) (spectrificationStepUnit Y)
    f (spectrificationStepMap f) (spectrificationStepUnit_natural f).symm

/-- The constructed closed-cylinder step is an actual functor. -/
noncomputable def spectrificationCylinderFunctor : Prespectrum.{u} ⥤ Prespectrum.{u} where
  obj := spectrificationCylinderStep
  map := spectrificationCylinderMap
  map_id X := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    obtain ⟨p,rfl⟩ := mappingCylinderMk_surjective (spectrificationStepUnit X) n z
    rcases p with ⟨x,t⟩ | p
    · rfl
    · exact congrArg (fun q => mappingCylinderMk (spectrificationStepUnit X) n (.inr q))
        (congrArg (fun h : spectrificationStep X ⟶ spectrificationStep X => h.level n p)
          (spectrificationStepFunctor.map_id X))
  map_comp {X Y Z} f g := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    obtain ⟨p,rfl⟩ := mappingCylinderMk_surjective (spectrificationStepUnit X) n z
    rcases p with ⟨x,t⟩ | p
    · rfl
    · exact congrArg (fun q => mappingCylinderMk (spectrificationStepUnit Z) n (.inr q))
        (congrArg (fun h : spectrificationStep X ⟶ spectrificationStep Z => h.level n p)
          (spectrificationStepFunctor.map_comp f g))

/-- The actual step inclusions form a natural transformation. -/
noncomputable def spectrificationCylinderUnitNat :
    𝟭 Prespectrum.{u} ⟶ spectrificationCylinderFunctor where
  app := spectrificationCylinderUnit
  naturality _ _ f := (mappingCylinderInclusion_natural _ _ f (spectrificationStepMap f)
    (spectrificationStepUnit_natural f).symm).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
