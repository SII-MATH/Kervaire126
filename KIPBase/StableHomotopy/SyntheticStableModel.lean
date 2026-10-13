import KIPBase.StableHomotopy.StableModelCategory

/-!
# The chosen model for synthetic spectra

The synthetic category used below is the homotopy category of a chosen
point-set model. The model structure and its stability belong to that
point-set category; the public synthetic category is its localization.
-/

universe u v u' v'

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace KIPBase.Synthetic

open KIPBase.StableHomotopy

/-- A chosen point-set model for synthetic spectra and the stable model
structure on it. The triangulated structure is provided by stability on its
homotopy category. -/
structure SyntheticModelRealization where
  PointSet : Type u
  pointSetCategory : Category.{v} PointSet
  pointSetModelCategory : ModelCategory PointSet
  pointSetStable : @KIPBase.StableHomotopy.IsStableModelCategory PointSet
    pointSetCategory pointSetModelCategory

namespace SyntheticModelRealization

variable (M : SyntheticModelRealization.{u, v})

noncomputable instance instCategory : Category.{v} M.PointSet :=
  M.pointSetCategory

noncomputable instance instModelCategory : ModelCategory M.PointSet :=
  M.pointSetModelCategory

noncomputable instance instStableModelCategory :
    IsStableModelCategory M.PointSet := M.pointSetStable

/-- The synthetic category represented by the chosen point-set model. -/
abbrev homotopyCategory : Type u :=
  @Ho.{v, u} M.PointSet M.pointSetCategory M.pointSetModelCategory

end SyntheticModelRealization

/-- A category used by a generic synthetic construction is represented by the
homotopy category of a stable point-set model. The equivalence records that
the category parameter is the model's `Ho`, rather than itself carrying a
second model structure. -/
class SyntheticModelRealizationWitness (Syn : Type u')
    [Category.{v'} Syn] where
  model : SyntheticModelRealization.{u, v}
  homotopyEquivalence :
    CategoryTheory.Equivalence model.homotopyCategory Syn

/-- The foundational model input for synthetic spectra. -/
axiom standardSyntheticModel : SyntheticModelRealization.{u, v}

/-- The synthetic category is definitionally the homotopy category of the
chosen synthetic model. In particular, stable-model triangulation instances
apply directly to `Syn`; there is no further `Ho Syn` localization. -/
abbrev Syn : Type u :=
  SyntheticModelRealization.homotopyCategory.{u, v} standardSyntheticModel

noncomputable instance syntheticSynCategory : Category.{max u v, u} Syn := by
  letI : Category.{v} standardSyntheticModel.PointSet :=
    standardSyntheticModel.pointSetCategory
  letI : ModelCategory standardSyntheticModel.PointSet :=
    standardSyntheticModel.pointSetModelCategory
  exact (weakEquivalences standardSyntheticModel.PointSet).instCategoryLocalization

noncomputable instance standardSynModelRealizationWitness :
    SyntheticModelRealizationWitness Syn where
  model := standardSyntheticModel
  homotopyEquivalence := CategoryTheory.Equivalence.refl

noncomputable instance syntheticSynStableModelCategory :
    IsStableModelCategory standardSyntheticModel.PointSet :=
  standardSyntheticModel.pointSetStable

noncomputable instance syntheticSynPreadditive : Preadditive Syn :=
  standardSyntheticModel.pointSetStable.toPreadditive

noncomputable instance syntheticSynZeroObject : HasZeroObject Syn :=
  standardSyntheticModel.pointSetStable.homotopyHasZeroObject

noncomputable instance syntheticSynShift : HasShift Syn ℤ :=
  standardSyntheticModel.pointSetStable.homotopyShift

noncomputable instance syntheticSynShiftAdditive :
    ∀ n : ℤ, Functor.Additive (shiftFunctor Syn n) :=
  standardSyntheticModel.pointSetStable.homotopyShiftAdditive

noncomputable instance syntheticSynPretriangulated : Pretriangulated Syn :=
  standardSyntheticModel.pointSetStable.homotopyPretriangulated

end KIPBase.Synthetic
