module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Excision.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.HomotopyExtension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits KIP126.Topology.SmallObject

universe u

/-- A pushout along one actual simultaneous free-cubical attachment
preserves stable equivalences from cofibrant sources. Both the lifting
property and level homotopy extension come from the actual cells. -/
theorem cubicalCellularStageMap_pushout_stableEquivalence
    {S : Prespectrum.{u}} (X : Over S) (hX : IsCubicallyCofibrant X.left)
    (k : ℕ) {C D : Prespectrum.{u}} (hC : IsCubicallyCofibrant C)
    {g : (cellularStage cubicalCellBoundary X k).left ⟶ C}
    {i : (cellularStage cubicalCellBoundary X (k + 1)).left ⟶ D} {j : C ⟶ D}
    (h : IsPushout (cellularStageMap cubicalCellBoundary X k) g i j)
    (hg : stableEquivalences g) : stableEquivalences i :=
  isPushout_stableEquivalence_of_cubicalCofibration
    (cubicalCellularStage_isCubicallyCofibrant X hX k) hC
    (cubicalCellularStageMap_isCubicalCofibration X k) h
    (cubicalCellularStageMap_level_hasHomotopyExtension X k) hg

/-- The actual entire countable free-cubical attachment satisfies
stable excision, including its limit stage. No homotopy-extension
hypothesis is imposed on the inclusion. -/
theorem cubicalCellularInitialInclusion_pushout_stableEquivalence
    {S : Prespectrum.{u}} (X : Over S) (hX : IsCubicallyCofibrant X.left)
    {C D : Prespectrum.{u}} (hC : IsCubicallyCofibrant C)
    {g : X.left ⟶ C} {i : cellularReplacement cubicalCellBoundary X ⟶ D}
    {j : C ⟶ D}
    (h : IsPushout (colimit.ι (cellularSequence cubicalCellBoundary X) 0) g i j)
    (hg : stableEquivalences g) : stableEquivalences i :=
  isPushout_stableEquivalence_of_cubicalCofibration hX hC
    (cubicalCellularReplacement_initial_isCubicalCofibration X) h
    (cubicalCellularInitialInclusion_level_hasHomotopyExtension X) hg

end KIP126.StableHomotopy.Implementation.Prespectrum
