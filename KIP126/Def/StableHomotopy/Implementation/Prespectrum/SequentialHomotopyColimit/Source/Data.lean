module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The constructed stage comparisons become an actual natural isomorphism
of diagrams in the original stable localization. -/
noncomputable def sequentialHomotopySourceComparison (F : ℕ ⥤ Prespectrum.{u}) :
    sequentialHomotopyDiagram F ⋙ sourceLocalization ≅ F ⋙ sourceLocalization := by
  let α := Functor.whiskerRight (sequentialHomotopyComparison F) sourceLocalization
  letI (k : ℕ) : IsIso (α.app k) :=
    stableEquivalences.Q_inverts _ (sequentialHomotopyComparison_stableEquivalence F k)
  exact NatIso.ofComponents (fun k => asIso (α.app k)) (fun f => α.naturality f)

/-- The actual stable cocone from the original sequence to its constructed
topological telescope, using the inverses of the proved stage comparisons. -/
noncomputable def sourceSequentialHomotopyColimitCocone (F : ℕ ⥤ Prespectrum.{u}) :
    Cocone (F ⋙ sourceLocalization) :=
  (Cocone.precompose (sequentialHomotopySourceComparison F).inv).obj
    (sourceLocalization.mapCocone (sequentialColimitCocone (sequentialHomotopyDiagram F)))

end KIP126.StableHomotopy.Implementation.Prespectrum
