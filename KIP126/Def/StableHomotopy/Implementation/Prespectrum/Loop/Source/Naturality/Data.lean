module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Naturality.Functor.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Operation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual loop concatenation is natural for all localized morphisms,
including inverses of the original stable equivalences. -/
noncomputable def sourceLoopConcatNatTrans : sourceLoopPowerFunctor.{u} 2 ⟶ sourceLoopFunctor :=
  Localization.Construction.natTransExtension
    { app X := sourceLocalization.map (loopConcat X)
      naturality := by
        intro X Y f
        change (sourceLoopPowerFunctor 2).map (sourceLocalization.map f) ≫
            sourceLocalization.map (loopConcat Y) =
          sourceLocalization.map (loopConcat X) ≫ sourceLoopFunctor.map (sourceLocalization.map f)
        rw [sourceLoopPowerFunctor_map,sourceLoopFunctor_map,← Functor.map_comp,← Functor.map_comp,
          loopConcat_natural] }

/-- Actual loop reversal is likewise natural on the stable localization. -/
noncomputable def sourceLoopInverseNatTrans : sourceLoopFunctor.{u} ⟶ sourceLoopFunctor :=
  Localization.Construction.natTransExtension
    { app X := sourceLocalization.map (loopInverse X)
      naturality := by
        intro X Y f
        change sourceLoopFunctor.map (sourceLocalization.map f) ≫
            sourceLocalization.map (loopInverse Y) =
          sourceLocalization.map (loopInverse X) ≫ sourceLoopFunctor.map (sourceLocalization.map f)
        rw [sourceLoopFunctor_map,← Functor.map_comp,← Functor.map_comp,loopInverse_natural] }

end KIP126.StableHomotopy.Implementation.Prespectrum
