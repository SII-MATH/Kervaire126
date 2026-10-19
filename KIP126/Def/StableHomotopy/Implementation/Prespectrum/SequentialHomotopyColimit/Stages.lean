module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Homotopy.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Data
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Closed.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Data

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory _root_.Topology

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each constructed cylinder stage is actually stably equivalent to the
corresponding original stage, by the explicit cylinder deformation. -/
theorem sequentialCylinderProjection_stableEquivalence (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) :
    stableEquivalences ((sequentialCylinderProjection F).app n) := by
  cases n with
  | zero =>
    intro d
    change Function.Bijective ((stableHomotopyFunctor d).map (𝟙 (F.obj 0)))
    rw [CategoryTheory.Functor.map_id]
    exact Function.bijective_id
  | succ n => exact mappingCylinderProjection_stableEquivalence _

instance sequentialCylinderStage_level_t1Space (F : ℕ ⥤ Prespectrum.{u})
    [∀ k n, T1Space ((F.obj k).level n)] (k n : ℕ) :
    T1Space (((sequentialCylinderStage F k).left).level n) := by
  induction k with
  | zero => exact inferInstanceAs (T1Space ((F.obj 0).level n))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (T1Space (mappingCylinderLevel
      ((sequentialCylinderStage F k).hom ≫ F.map (homOfLE (Nat.le_succ k))) n))

/-- All transitions of the actual cylinder replacement are levelwise closed
embeddings when the original levels are T1. -/
theorem sequentialCylinderDiagram_successor_closed (F : ℕ ⥤ Prespectrum.{u})
    [∀ k n, T1Space ((F.obj k).level n)] (k n : ℕ) :
    IsClosedEmbedding (((sequentialCylinderDiagram F).map
      (homOfLE (Nat.le_succ k))).level n) := by
  change IsClosedEmbedding (((Functor.ofSequence (sequentialCylinderStageMap F)).map
    (homOfLE (Nat.le_succ k))).level n)
  rw [Functor.ofSequence_map_homOfLE_succ]
  change IsClosedEmbedding ((mappingCylinderInclusion
    ((sequentialCylinderStage F k).hom ≫ F.map (homOfLE (Nat.le_succ k)))).level n)
  exact mappingCylinderInclusion_isClosedEmbedding _ n

end KIP126.StableHomotopy.Implementation.Prespectrum

end
