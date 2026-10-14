module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Localization
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Cancellation
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

set_option backward.isDefEq.respectTransparency false

/-- The descended class is still detected by the specified ordinary source localization. -/
theorem homotopyStableEquivalences_eq_inverseImage_isomorphisms :
    homotopyStableEquivalences.{u} =
      (MorphismProperty.isomorphisms SourceCategory).inverseImage homotopyToSource := by
  funext X Y f
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  obtain ⟨g,rfl⟩ := homotopyQuotient_map_surjective f
  exact propext ((homotopyStableEquivalences_map_iff g).trans
    (stableEquivalence_iff_source_isIso g))

instance homotopyStableEquivalences_isMultiplicative :
    homotopyStableEquivalences.{u}.IsMultiplicative := by
  rw [homotopyStableEquivalences_eq_inverseImage_isomorphisms]
  infer_instance

/-- Actual homotopy pullbacks supply Ore squares, and their iterated path
diagonal construction supplies cancellation on the actual homotopy quotient. -/
instance homotopyStableEquivalences_hasRightCalculusOfFractions :
    homotopyStableEquivalences.{u}.HasRightCalculusOfFractions where
  exists_rightFraction := by
    rintro ⟨X⟩ ⟨Y⟩ φ
    obtain ⟨Z,f,s,hs,rfl⟩ := φ.cases
    rcases Z with ⟨Z⟩
    obtain ⟨f,rfl⟩ := homotopyQuotient_map_surjective f
    obtain ⟨s,rfl⟩ := homotopyQuotient_map_surjective s
    have hs' := (homotopyStableEquivalences_map_iff s).mp hs
    refine ⟨MorphismProperty.RightFraction.mk
      (homotopyQuotient.map (homotopyPullbackSnd s f))
      ((homotopyStableEquivalences_map_iff _).mpr
        (homotopyPullbackSnd_stableEquivalence s f hs'))
      (homotopyQuotient.map (homotopyPullbackFst s f)),?_⟩
    change homotopyQuotient.map (homotopyPullbackSnd s f) ≫ homotopyQuotient.map f =
      homotopyQuotient.map (homotopyPullbackFst s f) ≫ homotopyQuotient.map s
    rw [← Functor.map_comp,← Functor.map_comp]
    exact (homotopyQuotient_map_eq_iff _ _).mpr
      (pathHomotopic_symm ⟨homotopyPullbackStrictHomotopy s f⟩)
  ext := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g s hs h
    obtain ⟨f,rfl⟩ := homotopyQuotient_map_surjective f
    obtain ⟨g,rfl⟩ := homotopyQuotient_map_surjective g
    obtain ⟨s,rfl⟩ := homotopyQuotient_map_surjective s
    rw [← Functor.map_comp,← Functor.map_comp] at h
    obtain ⟨A,t,ht,hfg⟩ := pathHomotopic_cancel_stable f g s
      ((homotopyStableEquivalences_map_iff s).mp hs)
      ((homotopyQuotient_map_eq_iff _ _).mp h)
    refine ⟨homotopyQuotient.obj A,homotopyQuotient.map t,
      (homotopyStableEquivalences_map_iff _).mpr ht,?_⟩
    rw [← Functor.map_comp,← Functor.map_comp]
    exact (homotopyQuotient_map_eq_iff _ _).mpr hfg

/-- Equality of actual maps in the original source category is exactly
actual strict homotopy after precomposition by an actual stable equivalence. -/
theorem source_map_eq_iff_exists_homotopy_precomp {X Y : Prespectrum.{u}} (f g : X ⟶ Y) :
    sourceLocalization.map f = sourceLocalization.map g ↔
      ∃ (A : Prespectrum.{u}) (t : A ⟶ X), stableEquivalences t ∧
        Nonempty (StrictHomotopy (t ≫ f) (t ≫ g)) := by
  change homotopyToSource.map (homotopyQuotient.map f) =
    homotopyToSource.map (homotopyQuotient.map g) ↔ _
  rw [MorphismProperty.map_eq_iff_precomp homotopyToSource homotopyStableEquivalences]
  constructor
  · rintro ⟨⟨A⟩,t,ht,h⟩
    obtain ⟨t,rfl⟩ := homotopyQuotient_map_surjective t
    rw [← Functor.map_comp,← Functor.map_comp] at h
    exact ⟨A,t,(homotopyStableEquivalences_map_iff t).mp ht,
      (homotopyQuotient_map_eq_iff _ _).mp h⟩
  · rintro ⟨A,t,ht,h⟩
    refine ⟨homotopyQuotient.obj A,homotopyQuotient.map t,
      (homotopyStableEquivalences_map_iff t).mpr ht,?_⟩
    rw [← Functor.map_comp,← Functor.map_comp]
    exact (homotopyQuotient_map_eq_iff _ _).mpr h

end KIP126.StableHomotopy.Implementation.Prespectrum
