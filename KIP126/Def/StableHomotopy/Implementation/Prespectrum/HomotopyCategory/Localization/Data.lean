module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Quotient.Proofs
public import Mathlib.CategoryTheory.Localization.Predicate

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u v w

/-- The specified ordinary source category has the actual localization
universal property after quotienting strict maps by actual path homotopy. -/
noncomputable def homotopyToSourceUniversalProperty (E : Type v) [Category.{w} E] :
    CategoryTheory.Localization.StrictUniversalPropertyFixedTarget homotopyToSource.{u}
      homotopyStableEquivalences E where
  inverts := homotopyToSource_inverts
  lift F hF := (CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ stableEquivalences E).lift
    (homotopyQuotient ⋙ F)
    (fun _ _ f hf => hF _ ((homotopyStableEquivalences_map_iff f).mpr hf))
  fac F hF := by
    apply CategoryTheory.Quotient.lift_unique' pathHomotopic
    change homotopyQuotient ⋙ homotopyToSource ⋙ _ = homotopyQuotient ⋙ F
    rw [← Functor.assoc,homotopyToSource_fac]
    exact (CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ stableEquivalences E).fac _ _
  uniq F G h := by
    apply (CategoryTheory.Localization.strictUniversalPropertyFixedTargetQ stableEquivalences E).uniq
    have hh := congrArg (fun J => homotopyQuotient ⋙ J) h
    simpa only [← Functor.assoc,homotopyToSource_fac] using hh

end KIP126.StableHomotopy.Implementation.Prespectrum
