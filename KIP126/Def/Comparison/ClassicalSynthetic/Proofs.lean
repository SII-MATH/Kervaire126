import KIP126.Def.Comparison.ClassicalSynthetic.Data
import KIP126.Def.Synthetic.AdamsSequence.Proofs

namespace KIP126.Comparison.ClassicalSynthetic

open CategoryTheory
open KIP126.Classical.Adams
open KIP126.Core.SpectralSequence
open KIP126.Synthetic.SpectralSequence

universe v
noncomputable section

theorem forgetWeight_page_shape (r : AdamsPage) (i : Tridegree) :
    (syntheticAdamsShapeAt r).Rel i (syntheticAdamsTarget r i) :=
  syntheticAdamsShape_rel r i

theorem forgetWeight_differential_degree (r : AdamsPage) (i : Tridegree) :
    forgetWeight (syntheticAdamsTarget r i) =
      forgetWeight i + (r.toInt, r.toInt - 1) :=
  forgetWeight_add_shift r i

theorem synthetic_h₄_degree_forgets :
    forgetWeight syntheticH₄Degree = classicalH₄Degree := rfl

theorem synthetic_h₄_target_is_lambda_target :
    syntheticH₄TargetDegree = lambdaTarget syntheticH₀H₃SquaredDegree := rfl

/-- The maps induced from the cycle and boundary towers commute with dᵣ. -/
theorem ReindexedSpectralSequenceMap.differential_comm
    {classical : InternalClassicalSequence.{v}} {synthetic : SyntheticAdamsSS.{v}}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (b : Bidegree) :
    classicalDifferential classical comparison.firstPage comparison.differentialDegree r b ≫
        sourcePageMap comparison w r (b + (r, r - 1)) =
      sourcePageMap comparison w r b ≫ fixedWeightDifferential synthetic w r b :=
  (comparison.comm_d w r b).symm

theorem sourcePageMap_differential_naturality
    {classical : InternalClassicalSequence.{v}} {synthetic : SyntheticAdamsSS.{v}}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (b : Bidegree) :
    classicalDifferential classical comparison.firstPage comparison.differentialDegree r b ≫
        sourcePageMap comparison w r (b + (r, r - 1)) =
      sourcePageMap comparison w r b ≫ fixedWeightDifferential synthetic w r b :=
  comparison.differential_comm w r b

end
end KIP126.Comparison.ClassicalSynthetic
