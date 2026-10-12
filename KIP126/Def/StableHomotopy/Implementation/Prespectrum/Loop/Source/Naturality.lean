module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Naturality.Functor
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Group.Operation

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

@[simp] theorem sourceLoopConcatNatTrans_app (X : Prespectrum.{u}) :
    sourceLoopConcatNatTrans.app (sourceLocalization.obj X) = sourceLocalization.map (loopConcat X) :=
  Localization.Construction.NatTransExtension.app_eq _ X

@[simp] theorem sourceLoopInverseNatTrans_app (X : Prespectrum.{u}) :
    sourceLoopInverseNatTrans.app (sourceLocalization.obj X) = sourceLocalization.map (loopInverse X) :=
  Localization.Construction.NatTransExtension.app_eq _ X

/-- Internal concatenation commutes with an arbitrary localized target map. -/
theorem source_loopConcat_natural {X Y : Prespectrum.{u}}
    (b : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) :
    sourceLocalization.map (loopConcat X) ≫ sourceLoopFunctor.map b =
      sourcePiMap (fun _ : Fin 2 => sourceLoopFunctor.map b) ≫ sourceLocalization.map (loopConcat Y) := by
  have h := sourceLoopConcatNatTrans.naturality b
  rw [sourceLoopConcatNatTrans_app,sourceLoopConcatNatTrans_app] at h
  exact h.symm

theorem source_loopInverse_natural {X Y : Prespectrum.{u}}
    (b : sourceLocalization.obj X ⟶ sourceLocalization.obj Y) :
    sourceLocalization.map (loopInverse X) ≫ sourceLoopFunctor.map b =
      sourceLoopFunctor.map b ≫ sourceLocalization.map (loopInverse Y) := by
  have h := sourceLoopInverseNatTrans.naturality b
  rw [sourceLoopInverseNatTrans_app,sourceLoopInverseNatTrans_app] at h
  exact h.symm

end KIP126.StableHomotopy.Implementation.Prespectrum

end
