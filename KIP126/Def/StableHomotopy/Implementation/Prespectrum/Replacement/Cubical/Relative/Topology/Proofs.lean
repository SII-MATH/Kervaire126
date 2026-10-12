module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Relative.Proofs
public import KIP126.Def.Topology.Colimit.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.SmallObject

universe u

set_option backward.isDefEq.respectTransparency false

/-- Each original stage is closed embedded in the actual relative
free-cubical colimit, without a separation assumption on the initial map. -/
theorem cubicalCellularStageInclusion_level_isClosedEmbedding
    {S : Prespectrum.{u}} (X : Over S) (k n : ℕ) :
    IsClosedEmbedding ((colimit.ι (cellularSequence cubicalCellBoundary X) k).level n) := by
  let F := cellularSequence cubicalCellBoundary X
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  have hF : ∀ k, IsClosedEmbedding ((F ⋙ E).map (homOfLE (Nat.le_succ k))) := by
    intro k
    change IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n)
    dsimp only [F, cellularSequence]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact cubicalCellularStageMap_level_isClosedEmbedding X k n
  exact KIP126.Topology.isClosedEmbedding_nat_colimit (F ⋙ E)
    (E.mapCocone (colimit.cocone F)) (isColimitOfPreserves E (colimit.isColimit F)) hF k

/-- The actual relative free-cell colimit retains levelwise T1 separation
from its initial object. -/
theorem cubicalCellularReplacement_level_t1Space
    {S : Prespectrum.{u}} (X : Over S) [∀ n, T1Space (X.left.level n)] (n : ℕ) :
    T1Space ((cellularReplacement cubicalCellBoundary X).level n) := by
  let F := cellularSequence cubicalCellBoundary X
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  letI (k : ℕ) : T1Space ((F ⋙ E).obj k) := cubicalCellularStage_level_t1Space X k n
  have hF : ∀ k, IsClosedEmbedding ((F ⋙ E).map (homOfLE (Nat.le_succ k))) := by
    intro k
    change IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level n)
    dsimp only [F, cellularSequence]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact cubicalCellularStageMap_level_isClosedEmbedding X k n
  exact KIP126.Topology.t1Space_nat_colimit (F ⋙ E)
    (E.mapCocone (colimit.cocone F)) (isColimitOfPreserves E (colimit.isColimit F)) hF

/-- Actual relative attachment stages retain compact generation in the
original topology, provided it holds for their initial object. -/
theorem cubicalCellularStage_level_uCompactlyGeneratedSpace
    {S : Prespectrum.{u}} (X : Over S)
    [∀ n, UCompactlyGeneratedSpace.{u} (X.left.level n)] (k n : ℕ) :
    UCompactlyGeneratedSpace.{u} (((cellularStage cubicalCellBoundary X k).left).level n) := by
  induction k with
  | zero => exact inferInstanceAs (UCompactlyGeneratedSpace.{u} (X.left.level n))
  | succ k ih =>
    letI : UCompactlyGeneratedSpace.{u} (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj
        (cellularStage cubicalCellBoundary X k).left) := ih
    letI (i : ℕ × ℕ) : UCompactlyGeneratedSpace.{u}
        (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj (cubicalCellTarget i)) :=
      inferInstanceAs (UCompactlyGeneratedSpace.{u} ((cubicalCellTarget i).level n))
    let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
      cubicalCellBoundary (cellularStage cubicalCellBoundary X k).hom
    exact KIP126.Topology.uCompactlyGeneratedSpace_of_attachCells
      (attachCells_evaluation_forgetToTop c n)

/-- The genuine relative free-cell colimit retains compact generation,
using its actual levelwise topological colimit rather than a topology change. -/
theorem cubicalCellularReplacement_level_uCompactlyGeneratedSpace
    {S : Prespectrum.{u}} (X : Over S)
    [∀ n, UCompactlyGeneratedSpace.{u} (X.left.level n)] (n : ℕ) :
    UCompactlyGeneratedSpace.{u} ((cellularReplacement cubicalCellBoundary X).level n) := by
  let F := cellularSequence cubicalCellBoundary X
  let E := evaluationFunctor n ⋙ BasedSpace.forgetToTop
  letI : IsConnected ℕ := IsFiltered.isConnected _
  letI : PreservesColimitsOfSize.{0,0} (evaluationFunctor.{u} n) :=
    preservesSmallestColimits_of_preservesColimits _
  letI (k : ℕ) : UCompactlyGeneratedSpace.{u} ((F ⋙ E).obj k) :=
    cubicalCellularStage_level_uCompactlyGeneratedSpace X k n
  exact KIP126.Topology.uCompactlyGeneratedSpace_of_isColimit (F ⋙ E)
    (E.mapCocone (colimit.cocone F)) (isColimitOfPreserves E (colimit.isColimit F))

end KIP126.StableHomotopy.Implementation.Prespectrum
