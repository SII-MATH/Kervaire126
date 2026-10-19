module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Proofs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits Topology
universe u

instance prespectrumHasZeroMorphisms : HasZeroMorphisms Prespectrum.{u} where
  zero X Y := ⟨zeroMap X Y⟩
  comp_zero {X Y} f Z := by
    apply Hom.ext
    rfl
  zero_comp X {Y Z} f := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact f.point n

instance prespectrumHasZeroObject : HasZeroObject Prespectrum.{u} :=
  zeroPrespectrum_isZero.hasZeroObject

noncomputable instance sourceHasZeroMorphisms : HasZeroMorphisms SourceCategory.{u} :=
  source_zeroPrespectrum_isZero.hasZeroMorphisms

instance sourceHasZeroObject : HasZeroObject SourceCategory.{u} :=
  source_zeroPrespectrum_isZero.hasZeroObject

instance sourceLocalization_preservesZeroMorphisms : sourceLocalization.{u}.PreservesZeroMorphisms where
  map_zero X Y := by
    have hzero : (0 : X ⟶ Y) = (0 : X ⟶ zeroPrespectrum) ≫ (0 : zeroPrespectrum ⟶ Y) := by simp
    rw [hzero,Functor.map_comp]
    rw [source_zeroPrespectrum_isZero.eq_zero_of_tgt (sourceLocalization.map (0 : X ⟶ zeroPrespectrum))]
    exact zero_comp

end KIP126.StableHomotopy.Implementation.Prespectrum
