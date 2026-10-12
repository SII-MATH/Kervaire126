module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Order.Model.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

universe u

/-- The specified realization comparison with its proved original
basepoint equation, as a morphism of actual based spaces. -/
noncomputable def cubicalReplacementBasedRealizedComparison (X : Prespectrum.{u}) (n : ℕ) :
    cubicalReplacementRealizedModel X n ⟶ (cubicalReplacementFunctor.obj X).level n where
  map := (cubicalReplacementRealizedComparison X n).hom
  point := cubicalReplacementRealizedComparison_point X n

end KIP126.StableHomotopy.Implementation.Prespectrum
