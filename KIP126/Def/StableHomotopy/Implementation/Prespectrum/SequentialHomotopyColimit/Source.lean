module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialHomotopyColimit.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual source cocone computes the original stable homotopy colimit
in every degree, with precisely the same source arrows as the telescope. -/
noncomputable def sourceSequentialHomotopyColimitCocone_homotopy_isColimit
    (F : ℕ ⥤ Prespectrum.{u}) (d : ℤ) :
    IsColimit ((sourceStableHomotopyFunctor d).mapCocone
      (sourceSequentialHomotopyColimitCocone F)) := by
  let e := Functor.isoWhiskerRight (sequentialHomotopySourceComparison F)
    (sourceStableHomotopyFunctor d)
  change IsColimit ((sourceStableHomotopyFunctor d).mapCocone
    ((Cocone.precompose (sequentialHomotopySourceComparison F).inv).obj
      (sourceLocalization.mapCocone (sequentialColimitCocone (sequentialHomotopyDiagram F)))))
  apply IsColimit.ofIsoColimit ?_ (Functor.mapCoconePrecompose
    (H := sourceStableHomotopyFunctor d)).symm
  refine (IsColimit.precomposeInvEquiv e _).symm ?_
  apply IsColimit.ofIsoColimit ?_ (Functor.mapCoconeMapCocone
    (sequentialColimitCocone (sequentialHomotopyDiagram F))).symm
  rw [sourceStableHomotopyFunctor_fac]
  exact sequentialStableHomotopyCocone_isColimit (sequentialHomotopyDiagram F)
    (sequentialHomotopyDiagram_successor_closed F) d

end KIP126.StableHomotopy.Implementation.Prespectrum

end
