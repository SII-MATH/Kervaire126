module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Colimit.Instances
public import KIP126.Def.Topology.Coproduct.Wedge.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory CategoryTheory.Limits KIP126.Topology

universe u

/-- The explicit common-point quotient realizing a small based coproduct. -/
def wedge {J : Type u} (X : J → BasedSpace.{u}) : BasedSpace.{u} where
  space := TopCat.of (Wedge (fun j => X j) (fun j => (X j).point))
  point := wedgePoint (fun j => X j) (fun j => (X j).point)

def wedgeι {J : Type u} (X : J → BasedSpace.{u}) (j : J) : X j ⟶ wedge X where
  map := wedgeInclusion (fun j => X j) (fun j => (X j).point) j
  point := wedgeInclusion_point j

def wedgeDesc {J : Type u} {X : J → BasedSpace.{u}} {Y : BasedSpace.{u}}
    (f : ∀ j, X j ⟶ Y) : wedge X ⟶ Y where
  map := KIP126.Topology.wedgeDesc (fun j => X j) (fun j => (X j).point)
    Y.point (fun j => (f j).map) (fun j => (f j).point)
  point := rfl

def wedgeCofan {J : Type u} (X : J → BasedSpace.{u}) : Cofan X :=
  Cofan.mk (wedge X) (wedgeι X)

end KIP126.StableHomotopy.Implementation.BasedSpace
