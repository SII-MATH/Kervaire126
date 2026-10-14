module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Universal

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- An actual strict square induces its ordinary quotient map. -/
def cofiberMap {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : pointSetCofiber f ⟶ pointSetCofiber g :=
  cofiberDesc f (b ≫ cofiberProjection g) (by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    change (cofiberProjection g).level n (b.level n (f.level n x)) = _
    rw [show b.level n (f.level n x) = g.level n (a.level n x) from
      congrArg (fun e : X ⟶ Y' => e.level n x) h,cofiberProjection_image]
    rfl)
end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

@[reassoc] theorem cofiberProjection_map {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    cofiberProjection f ≫ cofiberMap a b h = b ≫ cofiberProjection g := rfl

@[simp] theorem cofiberMap_id {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    cofiberMap (f := f) (g := f) (𝟙 X) (𝟙 Y) (by simp) = 𝟙 _ := by
  apply cofiberHom_ext f
  simp only [cofiberProjection_map,Category.id_comp,Category.comp_id]

theorem cofiberMap_comp {X Y X' Y' X'' Y'' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} {k : X'' ⟶ Y''}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (a' : X' ⟶ X'') (b' : Y' ⟶ Y'') (h' : g ≫ b' = a' ≫ k) :
    cofiberMap a b h ≫ cofiberMap a' b' h' =
      cofiberMap (a ≫ a') (b ≫ b') (by rw [← Category.assoc,h,Category.assoc,h',Category.assoc]) := by
  apply cofiberHom_ext f
  simp only [cofiberProjection_map_assoc,cofiberProjection_map,Category.assoc]
end KIP126.StableHomotopy.Implementation.Prespectrum

end
