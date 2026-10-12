module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Category.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.CompletedSpectrum

/-- The actual one-point prespectrum, equipped with its proved locality. -/
def zeroSpectrum : CompletedSpectrum where
  spectrum := Prespectrum.zeroPrespectrum
  isLocal := Prespectrum.isHF2Local_of_source_isZero _ Prespectrum.source_zeroPrespectrum_isZero

end KIP126.StableHomotopy.Implementation.CompletedSpectrum
