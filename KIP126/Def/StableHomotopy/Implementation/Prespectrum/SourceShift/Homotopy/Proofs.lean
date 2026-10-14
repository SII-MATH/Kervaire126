module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
universe u

theorem stableHomotopy_iterateSuspension_finite (X : Prespectrum.{u}) (n : ℕ) (d : ℤ)
    [Finite (StableHomotopy X (d-n))] :
    Finite (StableHomotopy ((suspension^[n]) X) d) :=
  Finite.of_equiv _ (stableHomotopyIterateSuspensionEquiv X n d).symm

theorem stableHomotopy_iterateDesuspension_finite (X : Prespectrum.{u}) (n : ℕ) (d : ℤ)
    [Finite (StableHomotopy X (d+n))] :
    Finite (StableHomotopy ((desuspension^[n]) X) d) :=
  Finite.of_equiv _ (stableHomotopyIterateDesuspensionEquiv X n d).symm

theorem stableHomotopy_iterateSuspension_subsingleton (X : Prespectrum.{u}) (n : ℕ) (d : ℤ)
    [Subsingleton (StableHomotopy X (d-n))] :
    Subsingleton (StableHomotopy ((suspension^[n]) X) d) :=
  (stableHomotopyIterateSuspensionEquiv X n d).injective.subsingleton

theorem stableHomotopy_iterateDesuspension_subsingleton (X : Prespectrum.{u}) (n : ℕ) (d : ℤ)
    [Subsingleton (StableHomotopy X (d+n))] :
    Subsingleton (StableHomotopy ((desuspension^[n]) X) d) :=
  (stableHomotopyIterateDesuspensionEquiv X n d).injective.subsingleton

end KIP126.StableHomotopy.Implementation.Prespectrum
