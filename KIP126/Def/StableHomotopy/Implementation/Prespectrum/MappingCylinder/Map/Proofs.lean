module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.MappingCylinder.Map.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

@[simp] theorem mappingCylinderMap_id {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (h : f ≫ 𝟙 Y = 𝟙 X ≫ f) : mappingCylinderMap f f (𝟙 X) (𝟙 Y) h = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  obtain ⟨p,rfl⟩ := mappingCylinderMk_surjective f n z
  cases p <;> rfl

@[simp] theorem mappingCylinderMap_comp {X Y X' Y' X'' Y'' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (k : X'' ⟶ Y'')
    (a : X ⟶ X') (b : Y ⟶ Y') (a' : X' ⟶ X'') (b' : Y' ⟶ Y'')
    (h : f ≫ b = a ≫ g) (h' : g ≫ b' = a' ≫ k)
    (hh : f ≫ (b ≫ b') = (a ≫ a') ≫ k) :
    mappingCylinderMap f g a b h ≫ mappingCylinderMap g k a' b' h' =
      mappingCylinderMap f k (a ≫ a') (b ≫ b') hh := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  obtain ⟨p,rfl⟩ := mappingCylinderMk_surjective f n z
  cases p <;> rfl

@[simp] theorem mappingCylinderInclusion_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    mappingCylinderInclusion f ≫ mappingCylinderMap f g a b h =
      a ≫ mappingCylinderInclusion g := rfl

@[simp] theorem mappingCylinderSection_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    mappingCylinderSection f ≫ mappingCylinderMap f g a b h =
      b ≫ mappingCylinderSection g := rfl

theorem mappingCylinderProjection_natural {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) :
    mappingCylinderMap f g a b h ≫ mappingCylinderProjection g =
      mappingCylinderProjection f ≫ b := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  obtain ⟨p,rfl⟩ := mappingCylinderMk_surjective f n z
  rcases p with ⟨x,t⟩ | y
  · exact (congrArg (fun k : X ⟶ Y' => k.level n x) h).symm
  · rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
