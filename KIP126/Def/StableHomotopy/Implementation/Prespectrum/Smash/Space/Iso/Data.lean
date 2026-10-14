module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory

/-- The original smash maps carry actual isomorphisms in both factors
to an actual strict prespectrum isomorphism. -/
noncomputable def spaceSmashIso {A B : BasedSpace.{0}} {X Y : Prespectrum.{0}}
    (e : A ≅ B) (i : X ≅ Y) : spaceSmash A X ≅ spaceSmash B Y where
  hom := spaceSmashMap e.hom i.hom
  inv := spaceSmashMap e.inv i.inv
  hom_inv_id := by rw [← spaceSmashMap_comp,e.hom_inv_id,i.hom_inv_id,spaceSmashMap_id]
  inv_hom_id := by rw [← spaceSmashMap_comp,e.inv_hom_id,i.inv_hom_id,spaceSmashMap_id]

end KIP126.StableHomotopy.Implementation.Prespectrum
