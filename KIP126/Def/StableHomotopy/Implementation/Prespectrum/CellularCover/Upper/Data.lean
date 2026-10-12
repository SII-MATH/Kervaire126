module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.CellularCover.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

/-- All original stable classes in degrees at least n index actual sphere summands. -/
abbrev SourceUpperSphereIndex (X : SourceCategory.{0}) (n : ℤ) :=
  Σ d : {d : ℤ // n ≤ d}, (sourceStableHomotopyAddFunctor d.val).obj X

noncomputable def sourceUpperSphereCover (X : SourceCategory.{0}) (n : ℤ) : SourceCategory.{0} :=
  ∐ fun a : SourceUpperSphereIndex X n => Prespectrum.sourceSphere a.1.val

/-- Each summand maps by its specified original represented stable class. -/
noncomputable def sourceUpperSphereCoverMap (X : SourceCategory.{0}) (n : ℤ) :
    sourceUpperSphereCover X n ⟶ X :=
  Sigma.desc (fun a => Prespectrum.sourceStableHomotopyEquiv X.as.obj a.1.val a.2)

end KIP126.StableHomotopy.Implementation
