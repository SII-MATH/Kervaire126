module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Bond.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual reduced mapping-cylinder prespectrum of a strict map. -/
noncomputable def mappingCylinder {X Y : Prespectrum.{u}} (f : X ⟶ Y) : Prespectrum.{u} where
  level := mappingCylinderLevel f
  bond := mappingCylinderBond f
  bond_point := mappingCylinderBond_point f
  bond_zero := mappingCylinderBond_zero f
  bond_one := mappingCylinderBond_one f

/-- Include the source at the bottom end of its cylinder. -/
noncomputable def mappingCylinderInclusion {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    X ⟶ mappingCylinder f where
  level n := ⟨fun x => mappingCylinderMk f n (.inl (x,0)),
    (mappingCylinderMk f n).continuous.comp
      (continuous_inl.comp (continuous_id.prodMk continuous_const))⟩
  point n := mappingCylinderMk_point f n 0
  bond _ _ _ := rfl

/-- Include the target as the attached end of the reduced mapping cylinder. -/
noncomputable def mappingCylinderSection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    Y ⟶ mappingCylinder f where
  level n := ⟨fun y => mappingCylinderMk f n (.inr y),
    (mappingCylinderMk f n).continuous.comp continuous_inr⟩
  point _ := rfl
  bond _ _ _ := rfl

/-- The projection collapses each attached cylinder to its image in the target. -/
noncomputable def mappingCylinderProjection {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    mappingCylinder f ⟶ Y where
  level n := mappingCylinderLift f n
    ⟨Sum.elim (fun z => f.level n z.1) id,
      ((f.level n).continuous.comp continuous_fst).sumElim continuous_id⟩
    (fun _ => f.point n) (fun _ => rfl)
  point _ := rfl
  bond n z t := by
    obtain ⟨a,rfl⟩ := mappingCylinderMk_surjective f n z
    rcases a with ⟨x,s⟩ | y
    · exact f.bond n x t
    · rfl

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
