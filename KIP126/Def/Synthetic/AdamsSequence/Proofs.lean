import KIP126.Def.Synthetic.AdamsSequence.Data

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory
open KIP126.Core.SpectralSequence

universe v
noncomputable section

@[simp] theorem syntheticAdamsShift_two :
    syntheticAdamsShift AdamsPage.two = (2, 1, 0) := rfl

@[simp] theorem syntheticAdamsTarget_two (i : Tridegree) :
    syntheticAdamsTarget AdamsPage.two i = (i.1 + 2, i.2.1 + 1, i.2.2) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;>
      simp [syntheticAdamsTarget, syntheticAdamsShift, syntheticAdamsRawShift,
        AdamsPage.two, AdamsPage.toInt]

@[simp] theorem syntheticAdamsShape_rel (r : AdamsPage) (i : Tridegree) :
    (syntheticAdamsShapeAt r).Rel i (syntheticAdamsTarget r i) := by
  simp [syntheticAdamsShapeAt, syntheticAdamsShape, syntheticAdamsTarget,
    syntheticAdamsShift, syntheticAdamsRawShift]

@[simp] theorem forgetWeight_nuDegree
    (b : KIP126.Classical.Adams.Bidegree) :
    forgetWeight (nuDegree b) = b := rfl

@[simp] theorem lambdaTarget_weight (i : Tridegree) :
    (lambdaTarget i).2.2 = i.2.2 - 1 := by
  simp [lambdaTarget, lambdaDegree, sub_eq_add_neg]

@[simp] theorem forgetWeight_add_shift (r : AdamsPage) (i : Tridegree) :
    forgetWeight (syntheticAdamsTarget r i) =
      forgetWeight i + (r.toInt, r.toInt - 1) := rfl

/-- Weight preservation follows from the fixed degree, even for a zero
 differential; it is not an additional field supplied by a model. -/
theorem weightPreserving_differential (r : AdamsPage) (i : Tridegree) :
    i.2.2 = (syntheticAdamsTarget r i).2.2 := by
  simp [syntheticAdamsTarget, syntheticAdamsShift, syntheticAdamsRawShift]

/-- Normalization changes only the indexing, not the internal page object. -/
theorem SyntheticAdamsSS.Page_eq (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) :
    A.Page r i = A.sequence.Page r i := by
  simp only [SyntheticAdamsSS.Page, KIP126.Core.SpectralSequence.Page, A.firstPage]

/-- The λ action commutes with the actual differential on E₂. -/
theorem SyntheticLambdaAction.lambdaMap_comm {A : SyntheticAdamsSS.{v}}
    (action : SyntheticLambdaAction A) (i : Tridegree) :
    lambdaMapFromAction action i ≫ A.d₂ (lambdaTarget i) ≫
        eqToHom (congrArg (A.Page 2) (show
          syntheticAdamsTarget AdamsPage.two (lambdaTarget i) =
            lambdaTarget (syntheticAdamsTarget AdamsPage.two i) by
          simp only [syntheticAdamsTarget, lambdaTarget]; abel)) =
      A.d₂ i ≫ lambdaMapFromAction action (syntheticAdamsTarget AdamsPage.two i) :=
  action.comm_d 2 i

end
end KIP126.Synthetic.SpectralSequence
