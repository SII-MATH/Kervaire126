module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Homotopy.Inverse.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The actual Puppe comparison from the cone of the cone inclusion to
the original suspension is a stable equivalence, with a strict based
homotopy inverse and without any extra hypotheses on the level spaces. -/
theorem coneIterationComparison_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (coneIterationComparison f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  refine ⟨⟨sourceLocalization.map (coneIterationInverse f), ?_, ?_⟩⟩
  · have h := source_map_eq_of_pathHomotopic ⟨coneIterationHomotopy f⟩
    simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using h.symm
  · have h := source_map_eq_of_pathHomotopic ⟨coneIterationInverseHomotopy f⟩
    simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using h

theorem coneIterationInverse_stableEquivalence {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    stableEquivalences (coneIterationInverse f) := by
  apply (stableEquivalence_iff_source_isIso _).mpr
  refine ⟨⟨sourceLocalization.map (coneIterationComparison f), ?_, ?_⟩⟩
  · have h := source_map_eq_of_pathHomotopic ⟨coneIterationInverseHomotopy f⟩
    simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using h
  · have h := source_map_eq_of_pathHomotopic ⟨coneIterationHomotopy f⟩
    simpa only [Functor.map_comp, CategoryTheory.Functor.map_id] using h.symm

end KIP126.StableHomotopy.Implementation.Prespectrum
