module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Compression.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open scoped unitInterval

/-- The chosen coordinate window inside the original fixed sphere,
using its original canonical cube representative. -/
def sphereWindow (n : ℕ) (a b : Fin n → I) : Set (sphereLevel n) :=
  sphereCube n '' {t | ∀ i, a i < t i ∧ t i < b i}

end KIP126.StableHomotopy.Implementation.Prespectrum
