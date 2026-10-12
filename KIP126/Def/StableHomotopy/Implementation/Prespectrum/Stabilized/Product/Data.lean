module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Stabilized.Category.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Proofs
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

/-- Arbitrary actual products stay in the stabilized T₁ full subcategory. -/
def stabilizedPiFunctor (J : Type) :
    (J → StabilizedPrespectrum.{u}) ⥤ StabilizedPrespectrum.{u} where
  obj X := ⟨⟨piPrespectrum (fun j => (X j).obj.obj),
    fun n => inferInstanceAs (T1Space (∀ j, (X j).obj.obj.level n))⟩,
    hasBijectiveStabilization_pi _ (fun j => (X j).property)⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk (piMap (fun j => (f j).hom.hom)))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    rfl

/-- The actual strict product adjunction before localization. -/
def stabilizedPiAdjunction (J : Type) :
    Functor.pi' (fun _ : J => 𝟭 StabilizedPrespectrum.{u}) ⊣ stabilizedPiFunctor J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ObjectProperty.homMk (ObjectProperty.homMk
            (piLift (fun j => (f j).hom.hom)))
          invFun := fun f j => ObjectProperty.homMk (ObjectProperty.homMk
            (f.hom.hom ≫ piProjection (fun j => (Y j).obj.obj) j))
          left_inv := fun f => rfl
          right_inv := fun f => rfl }
      homEquiv_naturality_left_symm := fun f g => rfl
      homEquiv_naturality_right := fun f g => rfl }

end KIP126.StableHomotopy.Implementation.Prespectrum
