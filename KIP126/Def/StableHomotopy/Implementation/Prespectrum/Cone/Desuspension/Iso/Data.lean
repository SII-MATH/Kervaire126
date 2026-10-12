module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Desuspension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- The specified literal mapping cone and padded desuspension commute
by an actual strict point-set isomorphism. -/
def coneDesuspensionIso {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    cone (desuspensionMap f) ≅ (cone f).desuspension where
  hom := coneDesuspension f
  inv := coneDesuspensionInv f
  hom_inv_id := coneDesuspension_hom_inv f
  inv_hom_id := coneDesuspension_inv_hom f

end KIP126.StableHomotopy.Implementation.Prespectrum
