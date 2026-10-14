module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.SmallObject KIP126.Topology.HomotopyLifting

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual free-cubical attachments are closed embeddings at every
level, for an arbitrary initial strict map. -/
theorem cubicalCellularStageMap_level_isClosedEmbedding
    {S : Prespectrum.{u}} (X : Over S) (k n : ℕ) :
    IsClosedEmbedding ((cellularStageMap cubicalCellBoundary X k).level n) := by
  let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
    cubicalCellBoundary (cellularStage cubicalCellBoundary X k).hom
  exact KIP126.Topology.isClosedEmbedding_of_attachCells
    (attachCells_evaluation_forgetToTop c n)
    (fun i => cubicalCellBoundary_level_isClosedEmbedding i n)

/-- Relative free-cubical attachment stages preserve the initial
levelwise T1 property in their original topology. -/
theorem cubicalCellularStage_level_t1Space {S : Prespectrum.{u}} (X : Over S)
    [∀ n, T1Space (X.left.level n)] (k n : ℕ) :
    T1Space (((cellularStage cubicalCellBoundary X k).left).level n) := by
  induction k with
  | zero => exact inferInstanceAs (T1Space (X.left.level n))
  | succ k ih =>
    letI : T1Space (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj
        (cellularStage cubicalCellBoundary X k).left) := ih
    letI (i : ℕ × ℕ) : NormalSpace
        (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj (cubicalCellTarget i)) :=
      inferInstanceAs (NormalSpace ((cubicalCellTarget i).level n))
    letI (i : ℕ × ℕ) : T1Space
        (((evaluationFunctor n) ⋙ BasedSpace.forgetToTop).obj (cubicalCellTarget i)) :=
      inferInstanceAs (T1Space ((cubicalCellTarget i).level n))
    let c := CategoryTheory.SmallObject.attachCellsιFunctorObjOfSmall.{u}
      cubicalCellBoundary (cellularStage cubicalCellBoundary X k).hom
    exact KIP126.Topology.t1Space_of_attachCells (attachCells_evaluation_forgetToTop c n)
      (fun i => cubicalCellBoundary_level_isClosedEmbedding i n)

/-- Compact free-cubical boundaries factor through an actual finite
stage of the relative construction, where the next attachment solves the
specified lifting problem. -/
theorem cubicalCellularComparison_hasLiftingProperty
    {S : Prespectrum.{u}} (X : Over S) [∀ n, T1Space (X.left.level n)] (i : ℕ × ℕ) :
    HasLiftingProperty (cubicalCellBoundary i) (cellularComparison cubicalCellBoundary X) := by
  constructor
  intro t b sq
  let F := cellularSequence cubicalCellBoundary X
  letI (k : ℕ) : T1Space ((F.obj k).level i.1) :=
    cubicalCellularStage_level_t1Space X k i.1
  have hF : ∀ k, IsClosedEmbedding ((F.map (homOfLE (Nat.le_succ k))).level i.1) := by
    intro k
    dsimp only [F, cellularSequence]
    rw [Functor.ofSequence_map_homOfLE_succ]
    exact cubicalCellularStageMap_level_isClosedEmbedding X k i.1
  obtain ⟨k, g, hg⟩ := free_map_factor_sequential_colimit F (colimit.cocone F)
    (colimit.isColimit F) i.1 hF (BasedSpace.adjoinPoint (cubeBoundaryObject i.2)) t
  obtain ⟨l, hl, hπ⟩ := cellularComparison_extension cubicalCellBoundary X i t b sq.w k g hg
  exact CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := hπ }

/-- The actual relative comparison has full cube-boundary lifting
at every level, provided only that the initial levels are T1. -/
theorem cubicalCellularComparison_level_hasCubeBoundaryLifting
    {S : Prespectrum.{u}} (X : Over S) [∀ n, T1Space (X.left.level n)] (n : ℕ) :
    HasCubeBoundaryLifting ((cellularComparison cubicalCellBoundary X).level n) :=
  hasCubeBoundaryLifting_of_cubicalCellBoundary _
    (cubicalCellularComparison_hasLiftingProperty X) n

/-- This actual relative comparison is a stable equivalence by its
proved level homotopy bijections. -/
theorem cubicalCellularComparison_stableEquivalence
    {S : Prespectrum.{u}} (X : Over S) [∀ n, T1Space (X.left.level n)] :
    stableEquivalences (cellularComparison cubicalCellBoundary X) :=
  stableEquivalence_of_cubicalCellBoundary_lifting _
    (cubicalCellularComparison_hasLiftingProperty X)

end KIP126.StableHomotopy.Implementation.Prespectrum
