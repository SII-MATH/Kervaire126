module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Coproduct.Proofs
public import KIP126.Def.Topology.Coproduct.Wedge.Subfamily.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory CategoryTheory.Limits
universe u

/-- The actual inclusion of a subfamily of the explicit based wedge. -/
def wedgeSubfamilyMap {J : Type u} (X : J → BasedSpace.{u}) (s : Set J) :
    wedge (fun j : s => X j.val) ⟶ wedge X where
  map := KIP126.Topology.wedgeSubfamilyInclusion (fun j => X j) (fun j => (X j).point) s
  point := rfl

/-- The subfamily inclusion in the chosen based coproduct, with its
original actual summand maps. -/
noncomputable def coproductSubfamilyMap {J : Type u} (X : J → BasedSpace.{u}) (s : Set J) :
    (∐ fun j : s => X j.val) ⟶ ∐ X :=
  Sigma.desc (fun j : s => Sigma.ι X j.val)

end KIP126.StableHomotopy.Implementation.BasedSpace
