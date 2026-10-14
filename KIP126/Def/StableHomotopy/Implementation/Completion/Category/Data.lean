module

public import KIP126.Def.StableHomotopy.Implementation.Completion

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

open CategoryTheory

/-- The actual full inclusion of local spectra into the ordinary source
category. It leaves the specified localized morphisms unchanged. -/
noncomputable def toSource : CompletedSpectrum ⥤ SourceCategory.{0} where
  obj X := sourceLocalization.obj X.spectrum
  map f := f

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
