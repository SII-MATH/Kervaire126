module

public import KIP126.Def.Topology.SimplicialRealization.Product.Compact.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Pullback.Finite.Data
public import KIP126.Def.Topology.SimplicialRealization.FiniteSupport.Proofs
public import Mathlib.CategoryTheory.Monoidal.Closed.Types

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Although the ordinary topological product comparison need not be a
homeomorphism, its underlying function is always a bijection. Forgetting
topology preserves colimits, and products of sets preserve all colimits. -/
theorem productComparison_bijective (X Y : SSet.{u}) :
    Function.Bijective (CartesianMonoidalCategory.prodComparison SSet.toTop X Y) := by
  let F := SSet.toTop.{u} ⋙ forget TopCat
  let α := CartesianMonoidalCategory.prodComparisonNatTrans F X
  let K := CostructuredArrow.proj uliftYoneda Y ⋙ uliftYoneda
  haveI : IsIso (Functor.whiskerLeft K α) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro j
    letI := stdSimplex_right_productComparison_isIso X j.left.len
    change IsIso ((forget TopCat).map
      (CartesianMonoidalCategory.prodComparison SSet.toTop X Δ[j.left.len]))
    infer_instance
  have h : IsIso (α.app Y) :=
    isIso_app_coconePt_of_preservesColimit K α _ (Presheaf.isColimitTautologicalCocone' Y)
  letI := h
  exact (ConcreteCategory.isIso_iff_bijective (α.app Y)).mp h

end KIP126.Topology.SimplicialRealization
