module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Data
public import KIP126.Def.StableHomotopy.Implementation.Realization.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Equalizer.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Opposite Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- Singular evaluation sends the actual chosen vertex exactly to the
original basepoint, by the adjunction triangle identity. -/
theorem singularEvaluation_point (A : BasedSpace.{u}) :
    singularEvaluation A (singularRealization A).point = A.point := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.right_triangle_components A.space) (op ⦋0⦌))
    (TopCat.toSSetObj₀Equiv.symm A.point)
  have he := congrArg TopCat.toSSetObj₀Equiv h
  change singularEvaluation A (singularRealization A).point =
    TopCat.toSSetObj₀Equiv (TopCat.toSSetObj₀Equiv.symm A.point) at he
  exact he.trans (TopCat.toSSetObj₀Equiv.apply_symm_apply A.point)

/-- Evaluation on a realized singular simplex is its original continuous map. -/
theorem singularEvaluation_simplex (A : BasedSpace.{u}) (n : ℕ)
    (σ : (TopCat.toSSet.obj A.space).obj (op ⦋n⦌))
    (t : stdSimplex ℝ (Fin (n+1))) :
    singularEvaluation A
      (KIP126.Topology.SimplicialRealization.simplexPoint (TopCat.toSSet.obj A.space) σ t) =
      A.space.toSSetObjEquiv (op ⦋n⦌) σ t := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sSetTopAdj.right_triangle_components A.space) (op ⦋n⦌)) σ
  exact congrArg (fun z => A.space.toSSetObjEquiv (op ⦋n⦌) z t) h

/-- Singular realization is a genuine good based space even when the
original based space has no separation or cofibration hypotheses. -/
theorem singularRealization_isGood (A : BasedSpace.{u}) :
    (singularRealization A).IsGood :=
  basedRealization_isGood _ _

end KIP126.StableHomotopy.Implementation
