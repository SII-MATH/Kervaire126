module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Product.Abelian.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyFunctor.Proofs
public import Mathlib.CategoryTheory.Localization.FiniteProducts

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

universe u

variable {J : Type}

theorem stablePiComparison_natural {X Y : J → Prespectrum.{u}}
    (f : ∀ j, X j ⟶ Y j) (d : ℤ) (x : StableHomotopy (piPrespectrum X) d) (j : J) :
    stablePiComparison Y d (stableHomotopyMap (piMap f) d x) j =
      stableHomotopyMap (f j) d (stablePiComparison X d x j) := by
  induction x using Quot.inductionOn with
  | h a => rfl

/-- Finite pointwise products of actual stable equivalences are stable equivalences. -/
theorem piMap_stableEquivalence [Finite J] {X Y : J → Prespectrum.{u}}
    (f : ∀ j, X j ⟶ Y j) (hf : ∀ j, stableEquivalences (f j)) :
    stableEquivalences (piMap f) := by
  intro d
  constructor
  · intro x y h
    apply (stablePiComparison_bijective X d).injective
    funext j
    apply (hf j d).injective
    simpa only [stablePiComparison_natural] using
      congrArg (fun z => stablePiComparison Y d z j) h
  · intro y
    choose x hx using fun j => (hf j d).surjective (stablePiComparison Y d y j)
    obtain ⟨z,hz⟩ := (stablePiComparison_bijective X d).surjective x
    refine ⟨z, (stablePiComparison_bijective Y d).injective (funext fun j => ?_)⟩
    rw [stablePiComparison_natural, hz]
    exact hx j

theorem stableEquivalences_eq_inverseImage_isomorphisms :
    stableEquivalences.{u} =
      (MorphismProperty.isomorphisms SourceCategory).inverseImage sourceLocalization := by
  funext X Y f
  exact propext (stableEquivalence_iff_source_isIso f)

instance stableEquivalences_respectsIso : stableEquivalences.{u}.RespectsIso := by
  rw [stableEquivalences_eq_inverseImage_isomorphisms]
  infer_instance

instance stableEquivalences_containsIdentities : stableEquivalences.{u}.ContainsIdentities := by
  rw [stableEquivalences_eq_inverseImage_isomorphisms]
  infer_instance

instance prespectrumHasProductsOfShape (J : Type) : HasProductsOfShape J Prespectrum.{u} := by
  refine ⟨fun F => ?_⟩
  letI : HasLimit (Discrete.functor (F.obj ∘ Discrete.mk)) :=
    ⟨⟨piFan (F.obj ∘ Discrete.mk), piFan_isLimit _⟩⟩
  exact hasLimit_of_iso Discrete.natIsoFunctor.symm

instance prespectrumHasFiniteProducts : HasFiniteProducts Prespectrum.{u} := ⟨fun _ => inferInstance⟩

instance stableEquivalences_stableUnderFiniteProducts :
    stableEquivalences.{u}.IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ := by
    apply MorphismProperty.IsStableUnderProductsOfShape.mk
    intro X Y _ _ f hf
    let eX := (piFan_isLimit X).conePointUniqueUpToIso (limit.isLimit (Discrete.functor X))
    let eY := (piFan_isLimit Y).conePointUniqueUpToIso (limit.isLimit (Discrete.functor Y))
    refine (stableEquivalences.arrow_mk_iso_iff (Arrow.isoMk eX eY ?_)).1
      (piMap_stableEquivalence f hf)
    apply Pi.hom_ext
    intro j
    change (eX.hom ≫ Limits.Pi.map f) ≫ Pi.π Y j = (piMap f ≫ eY.hom) ≫ Pi.π Y j
    rw [Category.assoc, Pi.map_π, ← Category.assoc]
    have hX := (piFan_isLimit X).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (Discrete.functor X)) (Discrete.mk j)
    have hY := (piFan_isLimit Y).conePointUniqueUpToIso_hom_comp
      (limit.isLimit (Discrete.functor Y)) (Discrete.mk j)
    change eX.hom ≫ Pi.π X j = piProjection X j at hX
    change eY.hom ≫ Pi.π Y j = piProjection Y j at hY
    rw [hX, Category.assoc, hY]
    rfl

/-- The ordinary localization has actual finite products, inherited from the
proved pointwise prespectrum products and their stable equivalences. -/
instance sourceHasFiniteProducts : HasFiniteProducts SourceCategory.{u} :=
  Localization.hasFiniteProducts sourceLocalization stableEquivalences

noncomputable instance sourceLocalization_preservesFiniteProducts :
    PreservesFiniteProducts sourceLocalization.{u} :=
  Localization.preservesFiniteProducts sourceLocalization stableEquivalences

/-- The localization of the displayed pointwise product cone is a limit cone. -/
noncomputable def sourcePiFan_isLimit [Finite J] (X : J → Prespectrum.{u}) :
    IsLimit (sourceLocalization.mapCone (piFan X)) :=
  isLimitOfPreserves sourceLocalization (piFan_isLimit X)

end KIP126.StableHomotopy.Implementation.Prespectrum
