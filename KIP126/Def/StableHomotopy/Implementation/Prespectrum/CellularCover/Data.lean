module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.Derived.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Additive.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

/-- The actual coproduct of degree-n source spheres indexed by the original
stable homotopy classes of X in that degree. -/
noncomputable def sourceSphereCover (X : SourceCategory.{0}) (n : ℤ) : SourceCategory.{0} :=
  ∐ fun _ : (sourceStableHomotopyAddFunctor n).obj X => Prespectrum.sourceSphere n

/-- The original represented class on each summand gives the specified
sphere-cover map into the original source object. -/
noncomputable def sourceSphereCoverMap (X : SourceCategory.{0}) (n : ℤ) :
    sourceSphereCover X n ⟶ X :=
  Sigma.desc (fun x => Prespectrum.sourceStableHomotopyEquiv X.as.obj n x)

end KIP126.StableHomotopy.Implementation
