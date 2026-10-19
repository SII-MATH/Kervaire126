module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Step.Data

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Apply a strict map to each of the actual recursively constructed stages. -/
noncomputable def spectrificationStagesMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    ∀ k, spectrificationStages X k ⟶ spectrificationStages Y k
  | 0 => f
  | k+1 => spectrificationCylinderMap (spectrificationStagesMap f k)

/-- The actual stage maps commute with the actual telescope transitions. -/
noncomputable def spectrificationDiagramMap {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    spectrificationDiagram X ⟶ spectrificationDiagram Y :=
  NatTrans.ofSequence (spectrificationStagesMap f) (fun k => by
    change (Functor.ofSequence (fun j => spectrificationCylinderUnit (spectrificationStages X j))).map
      (homOfLE (Nat.le_succ k)) ≫ spectrificationStagesMap f (k+1) =
      spectrificationStagesMap f k ≫
        (Functor.ofSequence (fun j => spectrificationCylinderUnit (spectrificationStages Y j))).map
          (homOfLE (Nat.le_succ k))
    rw [Functor.ofSequence_map_homOfLE_succ,Functor.ofSequence_map_homOfLE_succ]
    exact (spectrificationCylinderUnitNat.naturality (spectrificationStagesMap f k)).symm)

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
