module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Quotient.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- Equality in the quotient is exactly the existence of an actual strict
path homotopy, rather than an unexamined generated closure. -/
theorem homotopyQuotient_map_eq_iff {X Y : Prespectrum.{u}} (f g : X ⟶ Y) :
    homotopyQuotient.map f = homotopyQuotient.map g ↔ pathHomotopic f g :=
  CategoryTheory.Quotient.functor_map_eq_iff pathHomotopic f g

@[simp] theorem homotopyToSource_fac :
    homotopyQuotient.{u} ⋙ homotopyToSource = sourceLocalization :=
  CategoryTheory.Quotient.lift_spec _ _ _

@[simp] theorem homotopyToSource_map {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyToSource.map (homotopyQuotient.map f) = sourceLocalization.map f := rfl

@[simp] theorem homotopyStableEquivalences_map_iff {X Y : Prespectrum.{u}} (f : X ⟶ Y) :
    homotopyStableEquivalences (homotopyQuotient.map f) ↔ stableEquivalences f :=
  stableEquivalences.quotient_iff pathHomotopic f

/-- The original class of stable equivalences is exactly the inverse image
of the class on the actual homotopy quotient. -/
theorem stableEquivalences_homotopy_inverseImage :
    stableEquivalences.{u} = homotopyStableEquivalences.inverseImage homotopyQuotient :=
  stableEquivalences.eq_inverseImage_quotientFunctor pathHomotopic

/-- Every quotient morphism still has an actual strict representative. -/
theorem homotopyQuotient_map_surjective {X Y : Prespectrum.{u}}
    (f : homotopyQuotient.obj X ⟶ homotopyQuotient.obj Y) :
    ∃ g : X ⟶ Y, homotopyQuotient.map g = f :=
  CategoryTheory.Quotient.full_functor pathHomotopic |>.map_surjective f

/-- The descended functor inverts the actual stable equivalences on the quotient. -/
theorem homotopyToSource_inverts : homotopyStableEquivalences.{u}.IsInvertedBy homotopyToSource := by
  rintro ⟨X⟩ ⟨Y⟩ f ⟨g,hg,rfl⟩
  exact stableEquivalences.Q_inverts g hg

end KIP126.StableHomotopy.Implementation.Prespectrum
