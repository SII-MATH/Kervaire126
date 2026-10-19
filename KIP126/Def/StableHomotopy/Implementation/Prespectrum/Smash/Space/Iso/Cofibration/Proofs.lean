module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Iso.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Strict isomorphisms on both ends of an actual commuting square
transport the cubical left lifting property. -/
theorem isCubicalCofibration_iff_of_iso {X Y X' Y' : Prespectrum.{u}}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : f ≫ eY.hom = eX.hom ≫ g) :
    IsCubicalCofibration f ↔ IsCubicalCofibration g := by
  constructor
  · intro hf
    have hg : g = eX.inv ≫ f ≫ eY.hom := by
      rw [h, ← Category.assoc, eX.inv_hom_id, Category.id_comp]
    rw [hg]
    intro E B p hp
    exact IsCubicalCofibration.comp (isCubicalCofibration_of_isIso eX.inv)
      (IsCubicalCofibration.comp hf (isCubicalCofibration_of_isIso eY.hom)) p hp
  · intro hg
    have hf : f = eX.hom ≫ g ≫ eY.inv := by
      rw [← Category.assoc, ← h, Category.assoc, eY.hom_inv_id, Category.comp_id]
    rw [hf]
    intro E B p hp
    exact IsCubicalCofibration.comp (isCubicalCofibration_of_isIso eX.hom)
      (IsCubicalCofibration.comp hg (isCubicalCofibration_of_isIso eY.inv)) p hp

/-- A genuine based-space isomorphism preserves the cofibration property
of the original fixed-parameter smash map. -/
theorem spaceSmashMap_isCubicalCofibration_iff_of_iso {A B : BasedSpace.{0}}
    (e : A ≅ B) {X Y : Prespectrum.{0}} (f : X ⟶ Y) :
    IsCubicalCofibration (spaceSmashMap (𝟙 A) f) ↔
      IsCubicalCofibration (spaceSmashMap (𝟙 B) f) :=
  isCubicalCofibration_iff_of_iso (spaceSmashIso e (Iso.refl X))
    (spaceSmashIso e (Iso.refl Y)) _ _ (spaceSmashIso_natural e f)

end KIP126.StableHomotopy.Implementation.Prespectrum
