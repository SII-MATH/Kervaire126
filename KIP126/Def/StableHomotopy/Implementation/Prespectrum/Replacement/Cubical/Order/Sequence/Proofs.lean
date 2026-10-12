module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Order.Sequence.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cells.Geometry.Refinement.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open KIP126.Topology.SmallObject KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- The specified original replacement level is the actual topological
colimit of its ordinary cell-attachment stages. -/
theorem cubicalReplacementLevelCocone_isColimit (X : Prespectrum.{u}) (n : ℕ) :
    Nonempty (IsColimit (cubicalReplacementLevelCocone X n)) := by
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  exact ⟨isColimitOfPreserves (evaluationFunctor n ⋙ BasedSpace.forgetToTop)
    (colimit.isColimit _)⟩

/-- The actual successor map of the displayed level sequence attaches
ordinary cubes, retaining the original replacement maps. -/
theorem cubicalReplacementLevelSequence_attachCells (X : Prespectrum.{u}) (n k : ℕ) :
    Nonempty (AttachCells.{u} (cubeBoundaryInclusion.{u})
      ((cubicalReplacementLevelSequence X n).map (homOfLE (Nat.le_succ k)))) := by
  change Nonempty (AttachCells.{u} (cubeBoundaryInclusion.{u})
    (TopCat.ofHom (((cellularSequence cubicalCellBoundary
      (Over.mk (zeroMap zeroPrespectrum X))).map (homOfLE (Nat.le_succ k))).level n)))
  dsimp only [cellularSequence]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact cubicalCellularStageMap_level_attachCells _ k n

/-- These original successor maps are closed homotopy-extension
inclusions, the hypotheses needed by the actual telescope comparison. -/
theorem cubicalReplacementLevelSequence_closedHEP (X : Prespectrum.{u}) (n k : ℕ) :
    _root_.Topology.IsClosedEmbedding
      ((cubicalReplacementLevelSequence X n).map (homOfLE (Nat.le_succ k))) ∧
    KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      ((cubicalReplacementLevelSequence X n).map (homOfLE (Nat.le_succ k))) := by
  change _root_.Topology.IsClosedEmbedding
    (((cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))).map
      (homOfLE (Nat.le_succ k))).level n) ∧ _
  dsimp only [cubicalReplacementLevelSequence, Functor.comp_map, cellularSequence]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact ⟨cubicalReplacementStageMap_level_isClosedEmbedding X k n,
    cubicalReplacementStageMap_level_hasHomotopyExtension X k n⟩

/-- Every displayed stage inclusion preserves the specified original
replacement basepoint exactly. -/
theorem cubicalReplacementLevelCocone_inclusion_point (X : Prespectrum.{u}) (n k : ℕ) :
    (cubicalReplacementLevelCocone X n).ι.app k
      (((cellularStage cubicalCellBoundary
        (Over.mk (zeroMap zeroPrespectrum X)) k).left).level n).point =
        ((cubicalReplacementFunctor.obj X).level n).point :=
  (colimit.ι (cellularSequence cubicalCellBoundary
    (Over.mk (zeroMap zeroPrespectrum X))) k).point n

end KIP126.StableHomotopy.Implementation.Prespectrum
