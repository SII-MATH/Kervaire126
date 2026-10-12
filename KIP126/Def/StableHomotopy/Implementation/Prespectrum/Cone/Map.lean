module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Map

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u
/-- A strict commuting square induces the literal mapping-cone map,
keeping the original cone parameter. -/
def coneMap {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) : cone f ⟶ cone g :=
  coneLift f (b ≫ coneInclusion g) (a ≫ coneNullPath g)
    (by rw [Category.assoc,coneNullPath_zero,← Category.assoc,← h,Category.assoc])
    (by rw [Category.assoc,coneNullPath_one]; rfl)
end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

@[reassoc] theorem coneInclusion_map {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    coneInclusion f ≫ coneMap a b h = b ≫ coneInclusion g := rfl

@[reassoc] theorem coneNullPath_map {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    coneNullPath f ≫ pathMap (coneMap a b h) = a ≫ coneNullPath g := rfl

@[simp] theorem coneMap_inl {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) (n : ℕ) (y : Y.level n) :
    (coneMap a b h).level n (Quot.mk _ (.inl y)) = Quot.mk (ConeRelation g n) (.inl (b.level n y)) := rfl

@[simp] theorem coneMap_inr {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) (n : ℕ) (x : X.level n) (t : I) :
    (coneMap a b h).level n (Quot.mk _ (.inr (x,t))) = Quot.mk (ConeRelation g n) (.inr (a.level n x,t)) := rfl

@[reassoc] theorem coneToCofiber_map {X Y X' Y' : Prespectrum.{u}} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g) :
    coneMap a b h ≫ coneToCofiber g = coneToCofiber f ≫ cofiberMap a b h := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩)
  · rfl
  · exact ((cofiberMap a b h).point n).symm

@[simp] theorem coneMap_id {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    coneMap (f := f) (g := f) (𝟙 X) (𝟙 Y) (by simp) = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩) <;> rfl

theorem coneMap_comp {X Y X' Y' X'' Y'' : Prespectrum.{u}}
    {f : X ⟶ Y} {g : X' ⟶ Y'} {k : X'' ⟶ Y''}
    (a : X ⟶ X') (b : Y ⟶ Y') (h : f ≫ b = a ≫ g)
    (a' : X' ⟶ X'') (b' : Y' ⟶ Y'') (h' : g ≫ b' = a' ≫ k) :
    coneMap a b h ≫ coneMap a' b' h' =
      coneMap (a ≫ a') (b ≫ b') (by rw [← Category.assoc,h,Category.assoc,h',Category.assoc]) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro (y | ⟨x,t⟩) <;> rfl
end KIP126.StableHomotopy.Implementation.Prespectrum

end
