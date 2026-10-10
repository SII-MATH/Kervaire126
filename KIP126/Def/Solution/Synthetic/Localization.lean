import KIP126.Def.StableHomotopy.Implementation.Data
import KIP126.Def.Synthetic.Localization.Recovery.Proofs

namespace KIP126.Def.Solution

open CategoryTheory KIP126.StableHomotopy KIP126.Synthetic KIP126.Synthetic.Context

universe u v u' v'

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  {N : NuFunctorData C Syn}

/-- a09: the specified unit has an actual λ-invertible target and admits a
unique factorization of every map into every λ-invertible object. -/
theorem lambda_localization_unit (I : LambdaInversionInterface N) (X : Syn) :
    IsLambdaLocalizationMap (I.localization.unit.app X) :=
  I.localization.unit_isLocalizationMap X

/-- a09: the given ν followed by the same realization recovers the identity
as a natural isomorphism, conditional on the explicit inversion interface. -/
theorem nu_realization_recovery (I : LambdaInversionInterface N) :
    Nonempty (N.functor ⋙ I.recovery.realization ≅ 𝟭 C) :=
  ⟨I.recovery.nuRealizationIso⟩

end KIP126.Def.Solution
