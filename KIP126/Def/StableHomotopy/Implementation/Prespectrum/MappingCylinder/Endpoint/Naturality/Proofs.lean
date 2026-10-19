module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Endpoint.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The two original endpoint inclusions are strictly natural. -/
@[reassoc] theorem cylinderEndpoints_natural {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coprod.map f f ≫ cylinderEndpoints Y = cylinderEndpoints X ≫ cylinderFunctor.map f := by
  apply coprod.hom_ext
  · change coprod.inl ≫ coprod.map f f ≫ coprod.desc _ _ =
      coprod.inl ≫ coprod.desc _ _ ≫ mappingCylinderMap (𝟙 X) (𝟙 Y) f f (by simp)
    simp only [coprod.inl_map_assoc,coprod.inl_desc_assoc,coprod.inl_desc,
      mappingCylinderInclusion_natural]
  · change coprod.inr ≫ coprod.map f f ≫ coprod.desc _ _ =
      coprod.inr ≫ coprod.desc _ _ ≫ mappingCylinderMap (𝟙 X) (𝟙 Y) f f (by simp)
    simp only [coprod.inr_map_assoc,coprod.inr_desc_assoc,coprod.inr_desc,
      mappingCylinderSection_natural]

end KIP126.StableHomotopy.Implementation.Prespectrum
