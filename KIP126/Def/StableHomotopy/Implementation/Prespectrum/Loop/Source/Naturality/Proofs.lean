module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Loop.Source.Naturality.Data

@[expose] public section

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
