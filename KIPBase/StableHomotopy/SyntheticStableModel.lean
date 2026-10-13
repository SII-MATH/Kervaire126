import KIPBase.StableHomotopy.StableModelCategory
import KIPBase.Synthetic.Basic

/-!
# Stable model structure on synthetic spectra

The synthetic category is assumed to admit a stable model structure. This
interface records only the model structure and stability of its homotopy
category; it imposes no monoidal model-category compatibility.
-/

universe u v

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  HomotopicalAlgebra MonoidalCategory
open KIPBase.StableHomotopy

/-- The model-category data asserted for a synthetic category. This bundle
contains no monoidal model-category structure. -/
structure SyntheticStableModelData (Syn : Type u) [Category.{v} Syn] where
  modelCategory : ModelCategory Syn
  stable : @IsStableModelCategory Syn inferInstance modelCategory

/-- A synthetic category admits a stable model structure. Its existing
monoidal category structure is not required to satisfy any model-category
compatibility axiom. -/
axiom syntheticStableModelCategory (Syn : Type u) [Category.{v} Syn]
    [Preadditive Syn] :
  SyntheticStableModelData Syn

/-- The model structure postulated for the synthetic category, available as a
local instance to model-level constructions. -/
noncomputable instance syntheticModelCategoryInstance (Syn : Type u)
    [Category.{v} Syn] [Preadditive Syn] :
    ModelCategory Syn :=
  (syntheticStableModelCategory Syn).modelCategory

/-- Stability of the homotopy category, associated to the postulated model
structure. -/
noncomputable instance syntheticStabilityInstance (Syn : Type u)
    [Category.{v} Syn] [Preadditive Syn] :
    IsStableModelCategory Syn := by
  let D := syntheticStableModelCategory Syn
  letI : ModelCategory Syn := D.modelCategory
  exact D.stable

end KIPBase.Synthetic
