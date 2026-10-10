import KIP126.Def.Comparison.ClassicalSynthetic.Proofs

/-!
# Internal classical--synthetic regression

The examples verify the common family/object binding and that finite and
infinite page maps use the same internal cycle and boundary maps. No concrete
synthetic model or literature proof is selected here.
-/

namespace KIP126.Comparison.ClassicalSynthetic.Regression

open CategoryTheory
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
open KIP126.StableHomotopy
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence

universe u v u' v'
noncomputable section

example : syntheticAdamsPageLevel.firstPage = 2 := rfl
example (r : ℕ) : syntheticAdamsPageLevel.page r = r := rfl
example (r : ℕ) :
    syntheticAdamsPageLevel.cycleLevel r =
      syntheticAdamsPageLevel.quotientExponent r :=
  syntheticAdamsPageLevel.cycleLevel_eq_quotientExponent r

example {classical : InternalClassicalSequence.{v}} {synthetic : SyntheticAdamsSS.{v}}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w r : ℤ) (b : Bidegree) :
    classicalDifferential classical comparison.firstPage comparison.differentialDegree r b ≫
        sourcePageMap comparison w r (b + (r, r - 1)) =
      sourcePageMap comparison w r b ≫ fixedWeightDifferential synthetic w r b :=
  comparison.differential_comm w r b
example {classical : InternalClassicalSequence.{v}} {synthetic : SyntheticAdamsSS.{v}}
    (comparison : ReindexedSpectralSequenceMap classical synthetic)
    (w : ℤ) (b : Bidegree) :
    sourceEInftyMap comparison w b = (comparison.ambient w).pageMap b ⊤ := rfl

example (r : AdamsPage) (i : Tridegree) :
    (syntheticAdamsShapeAt r).Rel i (syntheticAdamsTarget r i) :=
  syntheticAdamsShape_rel r i

example (r : AdamsPage) (i : Tridegree) :
    i.2.2 = (syntheticAdamsTarget r i).2.2 :=
  weightPreserving_differential r i

example {A : SyntheticAdamsSS.{v}} (action : SyntheticLambdaAction A) (i : Tridegree) :
    lambdaMapFromAction action i ≫ A.d₂ (lambdaTarget i) ≫
        eqToHom (congrArg (A.Page 2) (show
          syntheticAdamsTarget AdamsPage.two (lambdaTarget i) =
            lambdaTarget (syntheticAdamsTarget AdamsPage.two i) by
          simp only [syntheticAdamsTarget, lambdaTarget]; abel)) =
      A.d₂ i ≫ lambdaMapFromAction action (syntheticAdamsTarget AdamsPage.two i) :=
  action.lambdaMap_comm i

example {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData Stable Syn)
    (X : Stable) (n : ℕ) :
    (F.nuQuotient N X n).sequence = F.functor.obj (XModLambdaN (N.functor.obj X) n) := rfl

example {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    [HasFunctorialCofiber (C := Syn)] (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) :
    F.quotientProjection X n =
      F.functor.map (HasFunctorialCofiber.cofibι (lambdaPow n X)) := rfl

example {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData Stable Syn) :
    F.nuSphereIso N = F.functor.mapIso N.unitIso := rfl

example : forgetWeight syntheticH₄Degree = classicalH₄Degree :=
  synthetic_h₄_degree_forgets

example : syntheticH₄TargetDegree = lambdaTarget syntheticH₀H₃SquaredDegree :=
  synthetic_h₄_target_is_lambda_target

end
end KIP126.Comparison.ClassicalSynthetic.Regression
