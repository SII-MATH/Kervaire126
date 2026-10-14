module

public import KIP126.Def.StableHomotopy.Implementation.Completion.Locality.Predicates
public import Mathlib.CategoryTheory.Limits.HasLimits

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits

universe v u

set_option backward.isDefEq.respectTransparency false

/-- Every actual source limit of HF₂-local objects is HF₂-local. -/
theorem SourceIsHF2Local.of_isLimit {J : Type u} [Category.{v} J]
    {F : J ⥤ SourceCategory.{0}} (c : Cone F) (hc : IsLimit c)
    (hF : ∀ j, SourceIsHF2Local (F.obj j)) : SourceIsHF2Local c.pt := by
  intro A B f hf
  constructor
  · intro a b hab
    change f ≫ a = f ≫ b at hab
    apply hc.hom_ext
    intro j
    apply (hF j f hf).injective
    simpa only [Category.assoc] using congrArg (fun k => k ≫ c.π.app j) hab
  · intro a
    choose g hg using fun j => (hF j f hf).surjective (a ≫ c.π.app j)
    have hg' (j) : f ≫ g j = a ≫ c.π.app j := hg j
    let s : Cone F :=
      { pt := B
        π :=
          { app := g
            naturality := by
              intro j k u
              change 𝟙 B ≫ g k = g j ≫ F.map u
              rw [Category.id_comp]
              apply (hF k f hf).injective
              change f ≫ g k = f ≫ (g j ≫ F.map u)
              rw [← Category.assoc, hg' j, hg' k, Category.assoc, c.w u] } }
    refine ⟨hc.lift s, hc.hom_ext (fun j => ?_)⟩
    rw [Category.assoc, hc.fac]
    exact hg' j

end KIP126.StableHomotopy.Implementation
