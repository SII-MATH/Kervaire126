module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

/-- The actual one-point prespectrum, equipped with its proved locality. -/
def zeroSpectrum : CompletedSpectrum where
  spectrum := Prespectrum.zeroPrespectrum
  isLocal := Prespectrum.isHF2Local_of_source_isZero _ Prespectrum.source_zeroPrespectrum_isZero

end KIP126.StableHomotopy.Implementation.CompletedSpectrum

end

section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory CategoryTheory.Limits

/-- The actual one-point local spectrum is a zero object of the local category. -/
theorem zeroSpectrum_isZero : IsZero zeroSpectrum where
  unique_to X := Prespectrum.source_zeroPrespectrum_isZero.unique_to
    (sourceLocalization.obj X.spectrum)
  unique_from X := Prespectrum.source_zeroPrespectrum_isZero.unique_from
    (sourceLocalization.obj X.spectrum)

instance hasZeroObject : HasZeroObject CompletedSpectrum := zeroSpectrum_isZero.hasZeroObject

/-- Zero morphisms are the actual ordinary source zero morphisms. -/
noncomputable instance hasZeroMorphisms : HasZeroMorphisms CompletedSpectrum where
  zero X Y := ⟨(0 : sourceLocalization.obj X.spectrum ⟶ sourceLocalization.obj Y.spectrum)⟩
  comp_zero {X Y} f Z := by
    exact comp_zero (C := SourceCategory.{0})
      (X := sourceLocalization.obj X.spectrum) (Y := sourceLocalization.obj Y.spectrum)
      (Z := sourceLocalization.obj Z.spectrum) (f := f)
  zero_comp X {Y Z} f := by
    exact zero_comp (C := SourceCategory.{0})
      (X := sourceLocalization.obj X.spectrum) (Y := sourceLocalization.obj Y.spectrum)
      (Z := sourceLocalization.obj Z.spectrum) (f := f)

instance toSource_preservesZeroMorphisms : toSource.PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The inclusion preserves the specified concrete zero object. -/
theorem toSource_zeroSpectrum_isZero : IsZero (toSource.obj zeroSpectrum) :=
  Prespectrum.source_zeroPrespectrum_isZero

end KIP126.StableHomotopy.Implementation.CompletedSpectrum

end
