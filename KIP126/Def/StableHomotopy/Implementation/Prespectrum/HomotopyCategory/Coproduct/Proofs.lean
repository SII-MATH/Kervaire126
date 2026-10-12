module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Coproduct.Data
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The strict coproduct retains its actual universal property after taking
strict homotopy classes. -/
noncomputable def homotopyCoproductCofan_isColimit {J : Type u}
    (X : J → Prespectrum.{u}) : IsColimit (homotopyCoproductCofan X) := by
  classical
  let r (c : Cofan (fun j => homotopyQuotient.obj (X j))) (j : J) : X j ⟶ c.pt.as :=
    (homotopyQuotient_map_surjective (c.inj j)).choose
  have hr (c : Cofan (fun j => homotopyQuotient.obj (X j))) (j : J) :
      homotopyQuotient.map (r c j) = c.inj j :=
    (homotopyQuotient_map_surjective (c.inj j)).choose_spec
  refine Cofan.IsColimit.mk _ (fun c => homotopyQuotient.map (Sigma.desc (r c))) ?_ ?_
  · intro c j
    change homotopyQuotient.map (Sigma.ι X j) ≫
      homotopyQuotient.map (Sigma.desc (r c)) = c.inj j
    rw [← homotopyQuotient.map_comp, Sigma.ι_desc, hr]
  · intro c m hm
    obtain ⟨g, rfl⟩ := homotopyQuotient_map_surjective m
    apply (homotopyQuotient_map_eq_iff _ _).mpr
    apply (pathHomotopic_coproduct_iff _ _).mpr
    intro j
    apply (homotopyQuotient_map_eq_iff _ _).mp
    rw [Sigma.ι_desc, hr]
    exact (homotopyQuotient.map_comp _ _).trans (hm j)

/-- All small coproducts exist in the quotient by actual strict homotopy. -/
instance homotopyCategoryHasCoproducts : HasCoproducts.{u} HomotopyCategory.{u} :=
  hasCoproducts_of_colimit_cofans
    (fun X => homotopyCoproductCofan (fun j => (X j).as))
    (fun X => homotopyCoproductCofan_isColimit (fun j => (X j).as))

/-- Taking actual strict homotopy classes preserves each small coproduct. -/
instance homotopyQuotient_preservesCoproduct {J : Type u} (X : J → Prespectrum.{u}) :
    PreservesColimit (Discrete.functor X) homotopyQuotient := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
  exact (Cofan.isColimitMapCoconeEquiv homotopyQuotient X
    (Cofan.mk _ (Sigma.ι X))).symm (homotopyCoproductCofan_isColimit X)

instance homotopyQuotient_preservesCoproductsOfShape (J : Type u) :
    PreservesColimitsOfShape (Discrete J) homotopyQuotient.{u} :=
  preservesColimitsOfShape_of_discrete _

end KIP126.StableHomotopy.Implementation.Prespectrum
