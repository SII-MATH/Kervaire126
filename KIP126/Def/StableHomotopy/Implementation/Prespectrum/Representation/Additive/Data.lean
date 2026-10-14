module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

/-- The unchanged ordinary source-sphere representation, now as an
additive equivalence for both actually constructed group structures. -/
noncomputable def sourceStableHomotopyAddEquiv (X : Prespectrum) (d : ℤ) :
    StableHomotopy X d ≃+ (sourceSphere d ⟶ sourceLocalization.obj X) where
  toEquiv := sourceStableHomotopyEquiv X d
  map_add' := sourceStableHomotopyEquiv_add X d

end KIP126.StableHomotopy.Implementation.Prespectrum
