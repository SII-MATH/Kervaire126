module

public import KIP126.Def.StableHomotopy.Context.Data
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

namespace KIP126.StableHomotopy
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {J : Type w} [HasProductsOfShape J C]

/-- On represented maps, the actual coefficient product comparison can be
proved through an approximation coefficient E. Only surjectivity of the
approximation on the product is needed; individual factors use bijectivity. -/
theorem tensor_piComparison_postcomp_bijective_of_approximation
    {E H : C} (f : E ⟶ H) (X : J → C) (W : C)
    [IsIso (piComparison (tensorLeft E) X)]
    (hprod : Function.Surjective (fun a : W ⟶ E ⊗ ∏ᶜ X => a ≫ (f ▷ ∏ᶜ X)))
    (hfactor : ∀ j, Function.Bijective (fun a : W ⟶ E ⊗ X j => a ≫ (f ▷ X j))) :
    Function.Bijective
      (fun a : W ⟶ H ⊗ ∏ᶜ X => a ≫ piComparison (tensorLeft H) X) := by
  let p : (∏ᶜ fun j => E ⊗ X j) ⟶ (∏ᶜ fun j => H ⊗ X j) :=
    Limits.Pi.map (fun j => f ▷ X j)
  have hp : Function.Bijective
      (fun a : W ⟶ ∏ᶜ (fun j => E ⊗ X j) => a ≫ p) := by
    constructor
    · intro a b hab
      apply Pi.hom_ext
      intro j
      apply (hfactor j).injective
      have h := congrArg (fun z => z ≫ Pi.π (fun j => H ⊗ X j) j) hab
      simpa only [p, Category.assoc, Pi.map_π] using h
    · intro b
      choose a ha using fun j => (hfactor j).surjective (b ≫ Pi.π _ j)
      refine ⟨Pi.lift a, ?_⟩
      apply Pi.hom_ext
      intro j
      simpa only [p, Category.assoc, Pi.map_π, Pi.lift_π_assoc] using ha j
  have hE : Function.Bijective
      (fun a : W ⟶ E ⊗ ∏ᶜ X => a ≫ piComparison (tensorLeft E) X) := by
    constructor
    · intro a b hab
      exact (cancel_mono (piComparison (tensorLeft E) X)).mp hab
    · intro b
      refine ⟨b ≫ inv (piComparison (tensorLeft E) X), ?_⟩
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hsquare :
      (f ▷ ∏ᶜ X) ≫ piComparison (tensorLeft H) X =
        piComparison (tensorLeft E) X ≫ p := by
    apply Pi.hom_ext
    intro j
    simp only [Category.assoc]
    change (f ▷ ∏ᶜ X) ≫ piComparison (tensorLeft H) X ≫ Pi.π (fun j => H ⊗ X j) j =
      piComparison (tensorLeft E) X ≫ p ≫ Pi.π (fun j => H ⊗ X j) j
    have hH : piComparison (tensorLeft H) X ≫ Pi.π (fun j => H ⊗ X j) j = H ◁ Pi.π X j :=
      piComparison_comp_π (tensorLeft H) X j
    have hE : piComparison (tensorLeft E) X ≫ Pi.π (fun j => E ⊗ X j) j = E ◁ Pi.π X j :=
      piComparison_comp_π (tensorLeft E) X j
    rw [hH, show p ≫ Pi.π (fun j => H ⊗ X j) j =
      Pi.π (fun j => E ⊗ X j) j ≫ (f ▷ X j) from Limits.Pi.map_π _ _,
      ← Category.assoc, hE]
    exact (whisker_exchange f (Pi.π X j)).symm
  constructor
  · intro a b hab
    obtain ⟨a, rfl⟩ := hprod a
    obtain ⟨b, rfl⟩ := hprod b
    apply congrArg (fun a => a ≫ (f ▷ ∏ᶜ X))
    apply hE.injective
    apply hp.injective
    change (a ≫ piComparison (tensorLeft E) X) ≫ p =
      (b ≫ piComparison (tensorLeft E) X) ≫ p
    simpa only [Category.assoc, hsquare] using hab
  · intro b
    obtain ⟨b, hb⟩ := hp.surjective b
    obtain ⟨a, ha⟩ := hE.surjective b
    refine ⟨a ≫ (f ▷ ∏ᶜ X), ?_⟩
    change (a ≫ (f ▷ ∏ᶜ X)) ≫ piComparison (tensorLeft H) X = _
    change a ≫ piComparison (tensorLeft E) X = b at ha
    change b ≫ p = _ at hb
    rw [Category.assoc, hsquare, ← Category.assoc]
    exact (congrArg (fun c => c ≫ p) ha).trans hb

end KIP126.StableHomotopy
