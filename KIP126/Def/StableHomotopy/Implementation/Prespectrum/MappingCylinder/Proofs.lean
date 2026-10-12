module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

@[simp] theorem mappingCylinderInclusion_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderInclusion f ≫ mappingCylinderProjection f = f := rfl

@[simp] theorem mappingCylinderSection_projection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinderSection f ≫ mappingCylinderProjection f = 𝟙 Y := rfl

@[simp] theorem mappingCylinderProjection_inl {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s : I) :
    (mappingCylinderProjection f).level n (mappingCylinderMk f n (.inl (x,s))) = f.level n x := rfl

@[simp] theorem mappingCylinderProjection_inr {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (y : Y.level n) :
    (mappingCylinderProjection f).level n (mappingCylinderMk f n (.inr y)) = y := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
