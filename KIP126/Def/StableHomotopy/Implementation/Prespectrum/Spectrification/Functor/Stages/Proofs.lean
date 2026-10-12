module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Stages.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

@[simp] theorem spectrificationStagesMap_id (X : Prespectrum.{u}) (k : ℕ) :
    spectrificationStagesMap (𝟙 X) k = 𝟙 (spectrificationStages X k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change spectrificationCylinderMap (spectrificationStagesMap (𝟙 X) k) = _
    rw [ih]
    exact spectrificationCylinderFunctor.map_id _

@[simp] theorem spectrificationStagesMap_comp {X Y Z : Prespectrum.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : ℕ) :
    spectrificationStagesMap (f ≫ g) k = spectrificationStagesMap f k ≫ spectrificationStagesMap g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change spectrificationCylinderMap (spectrificationStagesMap (f ≫ g) k) = _
    rw [ih]
    exact spectrificationCylinderFunctor.map_comp _ _

end KIP126.StableHomotopy.Implementation.Prespectrum
