module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Data
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- Replace a strict sequence by successive actual reduced mapping cylinders.
The displayed projection remembers the original object at every stage. -/
noncomputable def sequentialCylinderStage (F : ℕ ⥤ Prespectrum.{u}) : ∀ n, Over (F.obj n)
  | 0 => Over.mk (𝟙 (F.obj 0))
  | n+1 => Over.mk (mappingCylinderProjection
      ((sequentialCylinderStage F n).hom ≫ F.map (homOfLE (Nat.le_succ n))))

/-- The actual source-side inclusion at a successive cylinder stage. -/
noncomputable def sequentialCylinderStageMap (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) :
    (sequentialCylinderStage F n).left ⟶ (sequentialCylinderStage F (n+1)).left :=
  mappingCylinderInclusion
    ((sequentialCylinderStage F n).hom ≫ F.map (homOfLE (Nat.le_succ n)))

/-- The genuine sequential diagram of the constructed cylinders. -/
noncomputable def sequentialCylinderDiagram (F : ℕ ⥤ Prespectrum.{u}) : ℕ ⥤ Prespectrum.{u} :=
  Functor.ofSequence (sequentialCylinderStageMap F)

/-- The projections commute with every actual transition of the original
sequence, not only after localization or passage to homotopy groups. -/
noncomputable def sequentialCylinderProjection (F : ℕ ⥤ Prespectrum.{u}) :
    sequentialCylinderDiagram F ⟶ F :=
  NatTrans.ofSequence (fun n => (sequentialCylinderStage F n).hom) (by
    intro n
    change (Functor.ofSequence (sequentialCylinderStageMap F)).map
      (homOfLE (Nat.le_succ n)) ≫ _ = _
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact mappingCylinderInclusion_projection _)

end KIP126.StableHomotopy.Implementation.Prespectrum
