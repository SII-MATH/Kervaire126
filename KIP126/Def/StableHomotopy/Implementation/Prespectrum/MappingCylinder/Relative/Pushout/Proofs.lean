module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Relative.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Iso.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The relative-cylinder lifting theorem applies to any actual
pushout model retaining the endpoint and source-cylinder maps. -/
theorem IsCubicalCofibration.cylinderPushoutProduct_of_isPushout
    {X Y P : Prespectrum.{u}} {i : X ⟶ Y} (hi : IsCubicalCofibration i)
    {a : Y ⨿ Y ⟶ P} {b : cylinderFunctor.obj X ⟶ P}
    (h : IsPushout (coprod.map i i) (cylinderEndpoints X) a b)
    (j : P ⟶ cylinderFunctor.obj Y)
    (ha : a ≫ j = cylinderEndpoints Y) (hb : b ≫ j = cylinderFunctor.map i) :
    IsCubicalCofibration j := by
  have e : j = h.isoPushout.hom ≫ Prespectrum.cylinderPushoutProduct i := by
    apply h.hom_ext
    · rw [← Category.assoc,h.inl_isoPushout_hom]
      exact ha.trans (pushout.inl_desc _ _ _).symm
    · rw [← Category.assoc,h.inr_isoPushout_hom]
      exact hb.trans (pushout.inr_desc _ _ _).symm
  rw [e]
  intro E B p hp
  exact IsCubicalCofibration.comp (isCubicalCofibration_of_isIso h.isoPushout.hom)
    (IsCubicalCofibration.cylinderPushoutProduct hi) p hp

end KIP126.StableHomotopy.Implementation.Prespectrum
