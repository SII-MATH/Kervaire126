module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Product.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

/-- The actual strict product functor preserves pointwise stable equivalences
on the full subcategory, with arbitrary index set. -/
theorem stabilizedPiFunctor_map_stableEquivalence {J : Type}
    {X Y : J → StabilizedPrespectrum.{u}} (f : X ⟶ Y)
    (hf : ∀ j, stabilizedStableEquivalences (f j)) :
    stabilizedStableEquivalences ((stabilizedPiFunctor J).map f) :=
  piMap_stableEquivalence_of_stabilization
    (fun j => (X j).property) (fun j => (Y j).property)
    (fun j => (f j).hom.hom) hf

end KIP126.StableHomotopy.Implementation.Prespectrum
