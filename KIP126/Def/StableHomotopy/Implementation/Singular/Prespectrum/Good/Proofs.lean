module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Prespectrum
public import KIP126.Def.StableHomotopy.Implementation.Smash

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- This actual point-set construction has good levels; the assertion
does not assert that evaluation is a stable equivalence. -/
theorem singularPrespectrum_isGood (X : Prespectrum.{0}) :
    (singularPrespectrum X).IsGood :=
  singularPrespectrum_level_isGood X

end KIP126.StableHomotopy.Implementation
