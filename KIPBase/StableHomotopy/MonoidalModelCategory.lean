import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.PushoutProduct
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Symmetric Monoidal Model Categories

We define the notion of a symmetric monoidal model category, following
Hovey's *Model Categories* (Definition 4.2.6) and Schwede-Shipley's
*Algebras and modules in monoidal model categories*.

A symmetric monoidal model category is a model category `C` equipped with
a closed symmetric monoidal structure such that:
1. (Pushout-product axiom) The pushout-product `f □ g` of two cofibrations is a
   cofibration, and is a trivial cofibration if either factor is.
2. (Unit axiom) For every cofibrant replacement `q : QI ⟶ 𝟙_ C` of the unit,
   tensoring with a cofibrant object preserves this weak equivalence.

We also define the monoid axiom (Schwede-Shipley): every map in the class
obtained by closing `{f ▷ X | f ∈ trivialCof, X ∈ C}` under pushouts and
transfinite composition is a weak equivalence.

## Main definitions

- `PushoutProductAxiom`: the pushout-product axiom
- `Cofibrant`: an object is cofibrant if `⊥ ⟶ X` is a cofibration
- `UnitAxiom`: the unit axiom for the monoidal unit
- `MonoidAxiom`: the Schwede-Shipley monoid axiom
- `SymMonoidalModelCategory`: a symmetric monoidal model category
- `SymMonoidalModelCategoryWithMonoidAxiom`: additionally satisfies the monoid axiom

## References
- [M. Hovey, *Model Categories*, 1999, Chapter 4][hovey-model]
- [S. Schwede, B. Shipley, *Algebras and modules in monoidal model
  categories*][schwede-shipley-monoids]
-/

universe v u

namespace KIPBase.StableHomotopy

open HomotopicalAlgebra

open CategoryTheory Limits MonoidalCategory MorphismProperty

variable (C : Type u) [Category.{v} C]

/-! ### Cofibrantly generated model structures -/

/-- Generating cofibrations and generating trivial cofibrations for a model
category. The small object argument for the two generating classes yields the
functorial factorizations used in concrete homotopy constructions. -/
class CofibrantlyGeneratedModelCategory
    [ModelCategory C] where
  /-- A chosen class of generating cofibrations. -/
  generatingCofibrations : MorphismProperty C
  /-- A chosen class of generating trivial cofibrations. -/
  generatingTrivialCofibrations : MorphismProperty C
  /-- Maps right-orthogonal to the generating cofibrations are the trivial
  fibrations. -/
  generatingCofibrations_rlp :
    generatingCofibrations.rlp = trivialFibrations C
  /-- Maps right-orthogonal to the generating trivial cofibrations are the
  fibrations. -/
  generatingTrivialCofibrations_rlp :
    generatingTrivialCofibrations.rlp = fibrations C
  /-- The generating cofibrations permit the small object argument. -/
  smallObjectArgument_cofibrations :
    MorphismProperty.HasSmallObjectArgument.{u} generatingCofibrations
  /-- The generating trivial cofibrations permit the small object argument. -/
  smallObjectArgument_trivialCofibrations :
    MorphismProperty.HasSmallObjectArgument.{u} generatingTrivialCofibrations

namespace CofibrantlyGeneratedModelCategory

variable [ModelCategory C] (G : CofibrantlyGeneratedModelCategory C)

/-- A cofibrantly generated model category has functorial cofibration--trivial
fibration factorizations. -/
noncomputable def cofibrationTrivialFibrationFactorization :
    MorphismProperty.FunctorialFactorizationData
      (cofibrations C) (trivialFibrations C) := by
  letI := G.smallObjectArgument_cofibrations
  have hleft : G.generatingCofibrations.rlp.llp = cofibrations C := by
    rw [G.generatingCofibrations_rlp]
    exact MorphismProperty.llp_eq_of_wfs _ _
  rw [← hleft, ← G.generatingCofibrations_rlp]
  exact MorphismProperty.functorialFactorizationData
    G.generatingCofibrations.rlp.llp G.generatingCofibrations.rlp

/-- A cofibrantly generated model category has functorial trivial
cofibration--fibration factorizations. -/
noncomputable def trivialCofibrationFibrationFactorization :
    MorphismProperty.FunctorialFactorizationData
      (trivialCofibrations C) (fibrations C) := by
  letI := G.smallObjectArgument_trivialCofibrations
  have hleft : G.generatingTrivialCofibrations.rlp.llp =
      trivialCofibrations C := by
    rw [G.generatingTrivialCofibrations_rlp]
    exact MorphismProperty.llp_eq_of_wfs _ _
  rw [← hleft, ← G.generatingTrivialCofibrations_rlp]
  exact MorphismProperty.functorialFactorizationData
    G.generatingTrivialCofibrations.rlp.llp G.generatingTrivialCofibrations.rlp

private noncomputable def initialArrowMap {X Y : C} (f : X ⟶ Y) :
    Arrow.mk (initial.to X) ⟶ Arrow.mk (initial.to Y) :=
  Arrow.homMk (𝟙 ((Arrow.mk (initial.to X)).left)) f (by
    change 𝟙 (⊥_ C) ≫ initial.to Y = initial.to X ≫ f
    rw [Category.id_comp]
    exact (initial.to_comp f).symm)

/-- The functorial cofibrant replacement obtained by factoring every map from
the initial object as a cofibration followed by a trivial fibration. -/
noncomputable def cofibrantReplacementFunctor : C ⥤ C where
  obj X := G.cofibrationTrivialFibrationFactorization.Z.obj
    (Arrow.mk (initial.to X))
  map {X Y} f := G.cofibrationTrivialFibrationFactorization.Z.map
    (initialArrowMap C f)
  map_id X := by
    have h : initialArrowMap C (𝟙 X) = 𝟙 (Arrow.mk (initial.to X)) := by
      ext <;> simp [initialArrowMap]
    rw [h]
    exact (G.cofibrationTrivialFibrationFactorization.Z).map_id _
  map_comp f g := by
    have h : initialArrowMap C f ≫ initialArrowMap C g =
        initialArrowMap C (f ≫ g) := by
      ext
      · change 𝟙 (⊥_ C) ≫ 𝟙 (⊥_ C) = 𝟙 (⊥_ C)
        simp
      · rfl
    rw [← h]
    exact (G.cofibrationTrivialFibrationFactorization.Z).map_comp _ _

/-- The natural trivial fibration from the functorial cofibrant replacement
to the identity functor. -/
noncomputable def cofibrantReplacementCounit :
    G.cofibrantReplacementFunctor ⟶ 𝟭 C where
  app X := G.cofibrationTrivialFibrationFactorization.p.app
    (Arrow.mk (initial.to X))
  naturality X Y f := by
    exact G.cofibrationTrivialFibrationFactorization.p.naturality
      (initialArrowMap C f)

/-- Every value of the functorial replacement is cofibrant. -/
theorem cofibrantReplacement_isCofibrant (X : C) :
    IsCofibrant (G.cofibrantReplacementFunctor.obj X) := by
  exact (isCofibrant_iff_of_isInitial
    (G.cofibrationTrivialFibrationFactorization.i.app
      (Arrow.mk (initial.to X))) initialIsInitial).2
    ((cofibration_iff _).2
      (G.cofibrationTrivialFibrationFactorization.hi
        (Arrow.mk (initial.to X))))

/-- The replacement counit is a weak equivalence. -/
theorem cofibrantReplacementCounit_weakEquivalence (X : C) :
    weakEquivalences C (G.cofibrantReplacementCounit.app X) :=
  (G.cofibrationTrivialFibrationFactorization.hp
    (Arrow.mk (initial.to X))).2

noncomputable instance [G : CofibrantlyGeneratedModelCategory C] :
    MorphismProperty.HasFunctorialFactorization
      (cofibrations C) (trivialFibrations C) := by
  refine ⟨⟨G.cofibrationTrivialFibrationFactorization⟩⟩

noncomputable instance [G : CofibrantlyGeneratedModelCategory C] :
    MorphismProperty.HasFunctorialFactorization
      (trivialCofibrations C) (fibrations C) := by
  refine ⟨⟨G.trivialCofibrationFibrationFactorization⟩⟩

end CofibrantlyGeneratedModelCategory

/-! ### Cofibrant objects -/

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

/-- An object `X` is cofibrant if the unique map from the initial object to `X`
is a cofibration. -/
class Cofibrant (X : C) : Prop where
  cofib_from_initial : cofibrations C (initial.to X)

end Cofibrant

/-! ### The pushout-product axiom -/

section PushoutProductAxiom

variable [MonoidalCategory C] [HasPushouts C]
  [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- The pushout-product axiom states that the pushout-product `f □ g` of two
cofibrations is a cofibration, and is a trivial cofibration if either factor is.

This is equivalent to requiring that cofibrations are "closed under the
pushout-product" in the arrow category with its Day convolution monoidal
structure. -/
class PushoutProductAxiom : Prop where
  pushoutProduct_cofib {A B K L : C} (f : A ⟶ B) (g : K ⟶ L) :
    cofibrations C f → cofibrations C g →
      cofibrations C (MonoidalCategory.Arrow.pushoutProduct.obj
        (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  pushoutProduct_trivCofib_left {A B K L : C} (f : A ⟶ B) (g : K ⟶ L) :
    trivialCofibrations C f → cofibrations C g →
      trivialCofibrations C (MonoidalCategory.Arrow.pushoutProduct.obj
        (Arrow.mk f) |>.obj (Arrow.mk g)).hom
  pushoutProduct_trivCofib_right {A B K L : C} (f : A ⟶ B) (g : K ⟶ L) :
    cofibrations C f → trivialCofibrations C g →
      trivialCofibrations C (MonoidalCategory.Arrow.pushoutProduct.obj
        (Arrow.mk f) |>.obj (Arrow.mk g)).hom

end PushoutProductAxiom

/-! ### The unit axiom -/

section UnitAxiom

variable [MonoidalCategory C] [HasInitial C]
  [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- The unit axiom: if `q : QI ⟶ 𝟙_ C` is a weak equivalence from a cofibrant
object, then `q ▷ X : QI ⊗ X ⟶ 𝟙_ C ⊗ X` is a weak equivalence for every
cofibrant `X`.

When the monoidal unit `𝟙_ C` is itself cofibrant, this axiom holds
automatically. No cofibrancy assumption is made on `𝟙_ C` itself. -/
class UnitAxiom : Prop where
  tensor_cofibrantReplacement_weq {QI : C} (q : QI ⟶ 𝟙_ C) :
    Cofibrant C QI → weakEquivalences C q →
      ∀ (X : C) [Cofibrant C X], weakEquivalences C (q ▷ X)

end UnitAxiom

/-! ### The monoid axiom -/

section MonoidAxiom

variable [MonoidalCategory C] [HasPushouts C]
  [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]

/-- The class of maps `f ▷ X` (i.e., `f ⊗ id_X`) where `f` is a trivial cofibration
and `X` is any object. This class generates the monoid axiom closure. -/
def trivCofTensor : MorphismProperty C :=
  fun X' Y' h => ∃ (A B X : C) (f : A ⟶ B) (eX : A ⊗ X = X') (eY : B ⊗ X = Y'),
    trivialCofibrations C f ∧ h = eX ▸ eY ▸ (f ▷ X)

/-- The monoid axiom (Schwede-Shipley): every map in the closure of
`trivCofTensor C` under pushouts and arbitrary small transfinite composition
is a weak equivalence.

This axiom ensures that transferred model structures exist on categories
of monoids (ring spectra) and modules over a monoid. -/
class MonoidAxiom : Prop where
  pushout_transfinite_weq :
    (trivCofTensor C).pushouts.transfiniteCompositions.{u} ≤ weakEquivalences C

end MonoidAxiom

/-! ### Symmetric monoidal model categories -/

/-- A symmetric monoidal model category combines:
- A closed symmetric monoidal structure `(C, ⊗, 𝟙_ C, ihom)`
- A model category structure (cofibrations, fibrations, weak equivalences, CM1-CM5)
- The pushout-product axiom (compatibility of `⊗` with cofibrations)
- The unit axiom (cofibrant replacement of the unit is well-behaved)

When the unit `𝟙_ C` is cofibrant, the unit axiom is automatic.

## Key consequence
The pushout-product axiom is equivalent to requiring that for any cofibration
`f` and fibration `p`, the pullback-hom `f ⋔ p` is a fibration, which is
trivial if either `f` or `p` is. -/
class SymMonoidalModelCategory
    [ModelCategory C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [HasLimits C] [HasColimits C] [HasPushouts C] [HasInitial C] where
  pushoutProductAxiom : PushoutProductAxiom C
  unitAxiom : UnitAxiom C

namespace SymMonoidalModelCategory

variable [ModelCategory C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]
  [HasLimits C] [HasColimits C] [HasPushouts C] [HasInitial C]
  [SymMonoidalModelCategory C]

instance : PushoutProductAxiom C := SymMonoidalModelCategory.pushoutProductAxiom
instance : UnitAxiom C := SymMonoidalModelCategory.unitAxiom

/-- In a symmetric monoidal model category, the pushout-product of two
cofibrations is a cofibration. -/
theorem pushoutProduct_cofibration {A B K L : C} (f : A ⟶ B) (g : K ⟶ L)
    [Cofibration f] [Cofibration g] :
    cofibrations C (MonoidalCategory.Arrow.pushoutProduct.obj
      (Arrow.mk f) |>.obj (Arrow.mk g)).hom :=
  PushoutProductAxiom.pushoutProduct_cofib f g (mem_cofibrations f) (mem_cofibrations g)

/-- Tensoring a cofibration on the right with a cofibrant object gives a cofibration.
This follows from the pushout-product axiom applied to `f □ (⊥ → X)`. -/
theorem whiskerRight_cofibration {A B : C} (f : A ⟶ B) (X : C)
    [Cofibration f] [Cofibrant C X] :
    cofibrations C (f ▷ X) := by
  haveI : IsIso (f ▷ (⊥_ C)) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (tensorLeft A) (⊥_ C))
      (initialIsInitial.isInitialObj (tensorLeft B) (⊥_ C)) _
  rw [show f ▷ X = pushout.inr (f ▷ (⊥_ C)) (A ◁ (initial.to X)) ≫
      (MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk f) |>.obj
        (Arrow.mk (initial.to X))).hom from by
    have := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f (initial.to X)).inr_ι
    simp only [curriedTensor_map_app, Functor.PushoutObjObj.ofHasPushout_inr] at this
    exact this.symm]
  exact (cofibrations C).comp_mem _ _
    (mem_cofibrations _)
    (PushoutProductAxiom.pushoutProduct_cofib f (initial.to X)
      (mem_cofibrations f) (Cofibrant.cofib_from_initial))

/-- Tensoring a trivial cofibration with a cofibrant object gives a trivial
cofibration, by the pushout-product axiom. -/
theorem whiskerRight_trivialCofibration_of_pushoutProduct {A B : C} (f : A ⟶ B) (X : C)
    [Cofibration f] [WeakEquivalence f] [Cofibrant C X] :
    trivialCofibrations C (f ▷ X) := by
  haveI : IsIso (f ▷ (⊥_ C)) :=
    isIso_of_isInitial (initialIsInitial.isInitialObj (tensorLeft A) (⊥_ C))
      (initialIsInitial.isInitialObj (tensorLeft B) (⊥_ C)) _
  rw [show f ▷ X = pushout.inr (f ▷ (⊥_ C)) (A ◁ (initial.to X)) ≫
      (MonoidalCategory.Arrow.pushoutProduct.obj (Arrow.mk f) |>.obj
        (Arrow.mk (initial.to X))).hom from by
    have h := (Functor.PushoutObjObj.ofHasPushout (curriedTensor C) f (initial.to X)).inr_ι
    simp only [curriedTensor_map_app, Functor.PushoutObjObj.ofHasPushout_inr] at h
    exact h.symm]
  have hpp := PushoutProductAxiom.pushoutProduct_trivCofib_left f (initial.to X)
    (mem_trivialCofibrations (f := f)) (Cofibrant.cofib_from_initial)
  exact ⟨(cofibrations C).comp_mem _ _ (mem_cofibrations _) hpp.1,
    (weakEquivalences C).comp_mem _ _ (mem_weakEquivalences _) hpp.2⟩

/-- Ken Brown's lemma for tensoring with a cofibrant object. The pushout-product
axiom makes `- ⊗ X` preserve trivial cofibrations; hence it preserves weak
equivalences between cofibrant objects. -/
theorem whiskerRight_weakEquivalence_of_cofibrant {A B : C} (f : A ⟶ B)
    (hf : weakEquivalences C f) (hA : Cofibrant C A) (hB : Cofibrant C B)
    (X : C) [Cofibrant C X] : weakEquivalences C (f ▷ X) := by
  haveI : IsCofibrant A := by
    rw [isCofibrant_iff, cofibration_iff]
    exact hA.cofib_from_initial
  haveI : IsCofibrant B := by
    rw [isCofibrant_iff, cofibration_iff]
    exact hB.cofib_from_initial
  let F : CofibrantBrownFactorization f := Classical.choice inferInstance
  have hFi : weakEquivalences C F.i := by
    letI : WeakEquivalence f := (weakEquivalence_iff _).2 hf
    exact (weakEquivalence_iff _).1 (inferInstance : WeakEquivalence F.i)
  have hFp : weakEquivalences C F.p := by
    letI : WeakEquivalence F.i := (weakEquivalence_iff _).2 hFi
    letI : WeakEquivalence f := (weakEquivalence_iff _).2 hf
    exact (weakEquivalence_iff _).1
      (weakEquivalence_of_precomp_of_fac F.fac)
  have hFs : weakEquivalences C F.s := by
    letI : WeakEquivalence F.p := (weakEquivalence_iff _).2 hFp
    exact (weakEquivalence_iff _).1 (inferInstance : WeakEquivalence F.s)
  have hFiTensor : weakEquivalences C (F.i ▷ X) := by
    letI : Cofibration F.i := (cofibration_iff _).2 F.hi
    letI : WeakEquivalence F.i := (weakEquivalence_iff _).2 hFi
    exact (whiskerRight_trivialCofibration_of_pushoutProduct C F.i X).2
  have hFsTensor : weakEquivalences C (F.s ▷ X) := by
    letI : WeakEquivalence F.s := (weakEquivalence_iff _).2 hFs
    exact (whiskerRight_trivialCofibration_of_pushoutProduct C F.s X).2
  have hFpTensor : weakEquivalences C (F.p ▷ X) := by
    have hsection : F.s ▷ X ≫ F.p ▷ X = 𝟙 (B ⊗ X) := by
      rw [← comp_whiskerRight, F.s_p, id_whiskerRight]
    letI : WeakEquivalence (F.s ▷ X) := (weakEquivalence_iff _).2 hFsTensor
    letI : WeakEquivalence (𝟙 (B ⊗ X)) := by infer_instance
    exact (weakEquivalence_iff _).1 (weakEquivalence_of_precomp_of_fac hsection)
  have hfac : f ▷ X = F.i ▷ X ≫ F.p ▷ X := by
    rw [← comp_whiskerRight, F.fac]
  rw [hfac]
  exact (weakEquivalences C).comp_mem _ _ hFiTensor hFpTensor

/-- Tensor products of cofibrant objects are cofibrant. The proof uses the
pushout-product axiom and transports along the symmetry because the initial
object occurs on the left of `initial.to Y`. -/
theorem tensor_cofibrant {X Y : C} (hX : Cofibrant C X) (hY : Cofibrant C Y) :
    Cofibrant C (X ⊗ Y) := by
  letI : Cofibrant C X := hX
  letI : Cofibrant C Y := hY
  have hsource : IsInitial ((⊥_ C) ⊗ X) :=
    (initialIsInitial.isInitialObj (tensorLeft X) (⊥_ C)).ofIso (β_ X (⊥_ C))
  letI : Cofibration (initial.to Y) := (cofibration_iff _).2 hY.cofib_from_initial
  have hmap : Cofibration ((initial.to Y) ▷ X) :=
    (cofibration_iff _).2 (whiskerRight_cofibration C (initial.to Y) X)
  have hYX : IsCofibrant (Y ⊗ X) :=
    (isCofibrant_iff_of_isInitial ((initial.to Y) ▷ X) hsource).2
      hmap
  have hXY : IsCofibrant (X ⊗ Y) := by
    apply (cofibration_iff _).2
    apply ((cofibrations C).arrow_mk_iso_iff
      (Arrow.isoMk' (initial.to (Y ⊗ X)) (initial.to (X ⊗ Y))
        (Iso.refl _) (β_ Y X) (by exact Subsingleton.elim _ _))).mp
    exact (cofibration_iff _).1 hYX
  exact ⟨(cofibration_iff _).1 hXY⟩

/-- If `f` and `g` are weak equivalences between cofibrant objects, then their
point-set tensor product is a weak equivalence. This is the homotopy-invariance
input used to define the derived tensor product on `Ho C`. -/
theorem tensorHom_weakEquivalence_of_cofibrant
    {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)
    (hf : weakEquivalences C f) (hg : weakEquivalences C g)
    (hA : Cofibrant C A) (hB : Cofibrant C B)
    (hX : Cofibrant C X) (hY : Cofibrant C Y) :
    weakEquivalences C (f ⊗ₘ g) := by
  letI : Cofibrant C B := hB
  have h₁ : weakEquivalences C (f ▷ X) :=
    whiskerRight_weakEquivalence_of_cofibrant C f hf hA hB X
  have h₂ : weakEquivalences C (g ▷ B) :=
    whiskerRight_weakEquivalence_of_cofibrant C g hg hX hY B
  have hleft : weakEquivalences C (B ◁ g) := by
    rw [show B ◁ g = (β_ B X).hom ≫ (g ▷ B) ≫ (β_ B Y).inv by
      calc
        B ◁ g = (B ◁ g) ≫ (β_ B Y).hom ≫ (β_ B Y).inv := by simp
        _ = (β_ B X).hom ≫ (g ▷ B) ≫ (β_ B Y).inv := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ (β_ B Y).inv)
              (BraidedCategory.braiding_naturality_right B g)]
    simpa only [Category.assoc] using
      (MorphismProperty.RespectsIso.postcomp (weakEquivalences C)
        (β_ B Y).inv _
        (MorphismProperty.RespectsIso.precomp (weakEquivalences C)
          (β_ B X).hom _ h₂))
  rw [tensorHom_def]
  exact (weakEquivalences C).comp_mem _ _ h₁ hleft

/-- When the monoidal unit is cofibrant, the unit axiom follows from the
pushout-product axiom: tensoring with a cofibrant object preserves weak
equivalences between cofibrant objects by Ken Brown's lemma. -/
theorem unitAxiom_of_cofibrant_unit
    [Cofibrant C (𝟙_ C)] [PushoutProductAxiom C] : UnitAxiom C where
  tensor_cofibrantReplacement_weq := by
    intro QI q hQI hq X _
    exact whiskerRight_weakEquivalence_of_cofibrant C q hq hQI
      (inferInstance : Cofibrant C (𝟙_ C)) X

end SymMonoidalModelCategory

/-! ### With the monoid axiom -/

/-- A symmetric monoidal model category satisfying the monoid axiom.

This is the full structure needed to construct model structures on categories of:
- Monoids (ring spectra) in `C`
- Modules over a monoid `R` in `C`
- Algebras over a commutative monoid `R` in `C`

See Schwede-Shipley, *Algebras and modules in monoidal model categories*,
Theorem 4.1. -/
class SymMonoidalModelCategoryWithMonoidAxiom
    [ModelCategory C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
    [HasLimits C] [HasColimits C] [HasPushouts C] [HasInitial C]
    extends SymMonoidalModelCategory C where
  monoidAxiom : MonoidAxiom C

namespace SymMonoidalModelCategoryWithMonoidAxiom

variable [ModelCategory C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]
  [HasLimits C] [HasColimits C] [HasPushouts C] [HasInitial C]
  [SymMonoidalModelCategoryWithMonoidAxiom C]

instance : MonoidAxiom C := SymMonoidalModelCategoryWithMonoidAxiom.monoidAxiom

end SymMonoidalModelCategoryWithMonoidAxiom

end KIPBase.StableHomotopy
