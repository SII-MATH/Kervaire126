module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Bond.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderBond_inl {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (x : X.level n) (s t : I) :
    mappingCylinderBond f n (mappingCylinderMk f n (.inl (x,s)),t) =
      mappingCylinderMk f (n+1) (.inl (X.bond n (x,t),s)) := rfl

@[simp] theorem mappingCylinderBond_inr {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n : ℕ) (y : Y.level n) (t : I) :
    mappingCylinderBond f n (mappingCylinderMk f n (.inr y),t) =
      mappingCylinderMk f (n+1) (.inr (Y.bond n (y,t))) := rfl

theorem mappingCylinderBond_point {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ) (t : I) :
    mappingCylinderBond f n ((mappingCylinderLevel f n).point,t) =
      (mappingCylinderLevel f (n+1)).point := by
  change mappingCylinderMk f (n+1) (.inr (Y.bond n ((Y.level n).point,t))) = _
  rw [Y.bond_point]
  rfl

theorem mappingCylinderBond_zero {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : mappingCylinderLevel f n) :
    mappingCylinderBond f n (z,0) = (mappingCylinderLevel f (n+1)).point := by
  obtain ⟨a,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases a with ⟨x,s⟩ | y
  · rw [mappingCylinderBond_inl,X.bond_zero,mappingCylinderMk_point]
  · rw [mappingCylinderBond_inr,Y.bond_zero]; rfl

theorem mappingCylinderBond_one {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n : ℕ)
    (z : mappingCylinderLevel f n) :
    mappingCylinderBond f n (z,1) = (mappingCylinderLevel f (n+1)).point := by
  obtain ⟨a,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases a with ⟨x,s⟩ | y
  · rw [mappingCylinderBond_inl,X.bond_one,mappingCylinderMk_point]
  · rw [mappingCylinderBond_inr,Y.bond_one]; rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
