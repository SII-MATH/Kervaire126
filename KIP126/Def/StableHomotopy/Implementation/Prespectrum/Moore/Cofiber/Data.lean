module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Data
public import KIP126.Def.StableHomotopy.Context.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

set_option backward.isDefEq.respectTransparency false

/-- Actual cofiber choices in the original source category, constructed
from its proved distinguished-triangle existence and square completion.
The existing class records these choices without functoriality laws. -/
noncomputable instance sourceChosenCofiber : HasFunctorialCofiber (C := SourceCategory.{u}) := by
  classical
  choose Z i δ hT using (fun (X Y : SourceCategory.{u}) (f : X ⟶ Y) =>
    distinguished_cocone_triangle f)
  let m {X₁ Y₁ X₂ Y₂ : SourceCategory.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
      (a : X₁ ⟶ X₂) (b : Y₁ ⟶ Y₂) (h : a ≫ f₂ = f₁ ≫ b) :=
    complete_distinguished_triangle_morphism
      (Triangle.mk f₁ (i X₁ Y₁ f₁) (δ X₁ Y₁ f₁))
      (Triangle.mk f₂ (i X₂ Y₂ f₂) (δ X₂ Y₂ f₂))
      (hT X₁ Y₁ f₁) (hT X₂ Y₂ f₂) a b h.symm
  exact
    { cofib := fun {X Y} f => Z X Y f
      cofibι := fun {X Y} f => i X Y f
      cofibδ := fun {X Y} f => δ X Y f
      cofib_distinguished := fun {X Y} f => hT X Y f
      cofibMap := fun f₁ f₂ a b h => (m f₁ f₂ a b h).choose
      cofibMap_ι := fun f₁ f₂ a b h => (m f₁ f₂ a b h).choose_spec.1.symm
      cofibMap_δ := fun f₁ f₂ a b h => (m f₁ f₂ a b h).choose_spec.2.symm }

end KIP126.StableHomotopy.Implementation
