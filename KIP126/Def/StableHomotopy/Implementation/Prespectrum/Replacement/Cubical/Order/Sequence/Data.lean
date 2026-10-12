module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cells.Evaluation.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits KIP126.Topology.SmallObject

universe u

/-- The actual topological sequence underlying a specified level of the
original cubical prespectrum replacement. -/
noncomputable def cubicalReplacementLevelSequence (X : Prespectrum.{u}) (n : ℕ) :
    ℕ ⥤ TopCat.{u} :=
  cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X)) ⋙
    evaluationFunctor n ⋙ BasedSpace.forgetToTop

/-- The original replacement level, with its original stage maps, as a
cocone on the actual underlying topological sequence. -/
noncomputable def cubicalReplacementLevelCocone (X : Prespectrum.{u}) (n : ℕ) :
    Cocone (cubicalReplacementLevelSequence X n) :=
  (evaluationFunctor n ⋙ BasedSpace.forgetToTop).mapCocone (colimit.cocone
    (cellularSequence cubicalCellBoundary (Over.mk (zeroMap zeroPrespectrum X))))

end KIP126.StableHomotopy.Implementation.Prespectrum
