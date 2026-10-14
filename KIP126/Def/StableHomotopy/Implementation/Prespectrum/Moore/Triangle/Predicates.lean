module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Moore.Functor.Idempotence.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

universe u

/-- The scalar orthogonality condition proved for the actual Moore
construction: all maps from scalar-invertible source objects vanish. -/
def SourceIsScalarComplete (p : ℕ) (X : SourceCategory.{u}) : Prop :=
  ∀ U : SourceCategory.{u}, IsIso (p • 𝟙 U) → Subsingleton (U ⟶ X)

end KIP126.StableHomotopy.Implementation
