module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Derived.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- On actual stabilized T₁ inputs, the derived product is canonically
isomorphic to the localization of their original pointwise product. -/
noncomputable def sourceStabilizedPiIso {J : Type} (X : J → StabilizedPrespectrum.{u}) :
    sourceLocalization.obj (piPrespectrum (fun j => (X j).obj.obj)) ≅
      (sourceDerivedPiFunctor J).obj (fun j => sourceLocalization.obj (X j).obj.obj) :=
  ((stabilizedPiLocalizer J).catCommSq
    (Functor.pi (fun _ : J => stabilizedInclusion ⋙ t1Inclusion ⋙ sourceLocalization))
    (stabilizedInclusion ⋙ t1Inclusion ⋙ sourceLocalization)).iso.app X

end KIP126.StableHomotopy.Implementation.Prespectrum
