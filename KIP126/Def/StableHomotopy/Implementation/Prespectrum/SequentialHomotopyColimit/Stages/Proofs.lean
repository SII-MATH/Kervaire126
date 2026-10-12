module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Stages.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Closed.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Map.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Data

@[expose] public section

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
