module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The induced telescope map is exactly the constructed stage map on every stage. -/
@[simp] theorem spectrificationTelescopeMap_inclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) (k : ℕ) :
    sequentialColimitInclusion (spectrificationDiagram X) k ≫ spectrificationTelescopeMap f =
      spectrificationStagesMap f k ≫ sequentialColimitInclusion (spectrificationDiagram Y) k :=
  (sequentialColimitCocone_isColimit (spectrificationDiagram X)).fac _ k

@[simp] theorem spectrificationTelescopeMap_id (X : Prespectrum.{u}) :
    spectrificationTelescopeMap (𝟙 X) = 𝟙 (spectrificationTelescope X) := by
  apply (sequentialColimitCocone_isColimit (spectrificationDiagram X)).hom_ext
  intro k
  change sequentialColimitInclusion _ k ≫ _ = sequentialColimitInclusion _ k ≫ _
  rw [spectrificationTelescopeMap_inclusion,spectrificationStagesMap_id,
    Category.id_comp]
  exact (Category.comp_id _).symm

@[simp] theorem spectrificationTelescopeMap_comp {X Y Z : Prespectrum.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    spectrificationTelescopeMap (f ≫ g) = spectrificationTelescopeMap f ≫ spectrificationTelescopeMap g := by
  apply (sequentialColimitCocone_isColimit (spectrificationDiagram X)).hom_ext
  intro k
  change sequentialColimitInclusion _ k ≫ _ = sequentialColimitInclusion _ k ≫ _
  calc
    sequentialColimitInclusion (spectrificationDiagram X) k ≫ spectrificationTelescopeMap (f ≫ g) =
        spectrificationStagesMap (f ≫ g) k ≫ sequentialColimitInclusion (spectrificationDiagram Z) k :=
      spectrificationTelescopeMap_inclusion (f ≫ g) k
    _ = (spectrificationStagesMap f k ≫ spectrificationStagesMap g k) ≫
        sequentialColimitInclusion (spectrificationDiagram Z) k :=
      congrArg (fun a => a ≫ sequentialColimitInclusion (spectrificationDiagram Z) k)
        (spectrificationStagesMap_comp f g k)
    _ = spectrificationStagesMap f k ≫ (spectrificationStagesMap g k ≫
        sequentialColimitInclusion (spectrificationDiagram Z) k) := Category.assoc _ _ _
    _ = spectrificationStagesMap f k ≫ (sequentialColimitInclusion (spectrificationDiagram Y) k ≫
        spectrificationTelescopeMap g) :=
      congrArg (fun a => spectrificationStagesMap f k ≫ a) (spectrificationTelescopeMap_inclusion g k).symm
    _ = (spectrificationStagesMap f k ≫ sequentialColimitInclusion (spectrificationDiagram Y) k) ≫
        spectrificationTelescopeMap g := (Category.assoc _ _ _).symm
    _ = (sequentialColimitInclusion (spectrificationDiagram X) k ≫ spectrificationTelescopeMap f) ≫
        spectrificationTelescopeMap g :=
      congrArg (fun a => a ≫ spectrificationTelescopeMap g) (spectrificationTelescopeMap_inclusion f k).symm
    _ = sequentialColimitInclusion (spectrificationDiagram X) k ≫
        (spectrificationTelescopeMap f ≫ spectrificationTelescopeMap g) := Category.assoc _ _ _


/-- The original-spectrum inclusion is natural for the actual telescope maps. -/
theorem spectrificationTelescopeUnit_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    f ≫ spectrificationTelescopeUnit Y = spectrificationTelescopeUnit X ≫ spectrificationTelescopeMap f :=
  (spectrificationTelescopeMap_inclusion f 0).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
