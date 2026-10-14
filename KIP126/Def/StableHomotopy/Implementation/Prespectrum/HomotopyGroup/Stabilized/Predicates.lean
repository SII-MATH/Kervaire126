module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

/-- All the actual based cubical stabilization maps are bijective. -/
def HasBijectiveStabilization (X : Prespectrum.{u}) : Prop :=
  ∀ n r, Function.Bijective (stabilizeHomotopy X n r)

end KIP126.StableHomotopy.Implementation.Prespectrum
