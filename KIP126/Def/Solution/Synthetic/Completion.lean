import KIP126.Def.StableHomotopy.Implementation.Data

namespace KIP126.Def.Solution

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Synthetic KIP126.Synthetic.Context

universe u v u' v'
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)] [HasProductsOfShape ℕ Syn]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}

/-- a12: the two genuine residual-tower completeness conditions correspond. -/
theorem nu_lambdaComplete_iff (I : LambdaAdicCompletenessInterface H N) (X : C) :
    Classical.Adams.IsENilpotentComplete H.unit X ↔ IsLambdaComplete (N.functor.obj X) := by
  sorry

/-- a12: the same quotient maps, under the required completeness hypothesis,
exhibit νX as a sequential homotopy limit. No ordinary limit of homotopy
groups or unrestricted convergence assertion is substituted here. -/
theorem nu_lambdaAdicCompletion (I : LambdaAdicCompletenessInterface H N) (X : C)
    (hX : Classical.Adams.IsENilpotentComplete H.unit X) :
    Nonempty (LambdaAdicCompletion (I.tower X)) := by
  sorry

/-- The quotient restrictions and the actual residual λ transition form
the boundary square of the same selected cofiber triangles. -/
theorem nu_quotientResidualCompatible (I : LambdaAdicCompletenessInterface H N) (X : C) :
    (I.tower X).ResidualCompatible := by
  sorry

end KIP126.Def.Solution
