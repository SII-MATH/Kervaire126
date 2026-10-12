module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Functor.Step.Data

@[expose] public section

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
