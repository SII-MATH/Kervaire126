module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.FiniteOrder.Coherence.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Deformation.Realization.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The canonical correction of the chosen horn extension has one
actual order-cylinder factor for the whole two-parameter homotopy.
In particular its changing upper face is retained as an actual finite
order factor, rather than claimed to stay fixed. -/
theorem exists_singularOrderCylinderHorn_canonical_factored_homotopy
    (P V : Type u) [PartialOrder P] [Fintype V]
    (h : |nerve (WithTop P)| ≃ₜ stdSimplex ℝ V) (B : TopCat.{u})
    (ψ : nerve (OrderCylinderHorn P) ⟶ TopCat.toSSet.obj B) :
    ∃ r : C(|nerve (OrderCylinder (WithTop P))|,|nerve (OrderCylinderHorn P)|),
      ∃ a : nerve (OrderCylinder (WithTop P)) ⟶ TopCat.toSSet.obj B,
        orderCylinderHornInclusion P ≫ a = ψ ∧
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map a).hom =
          (sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp r)) ∧
        ∃ H : ((SSet.toTop.map ψ).hom.comp r).HomotopyRel (SSet.toTop.map a).hom
          (Set.range (SSet.toTop.map (orderCylinderHornInclusion P))),
          ∃ J : C(I × |nerve (OrderCylinder (WithTop P))|,
            |nerve (OrderCylinder (WithTop P))|), ∀ z, H z = SSet.toTop.map a (J z) := by
  let D := nerve (OrderCylinder (WithTop P))
  let i := orderCylinderHornInclusion P
  let ε := (sSetTopAdj.counit.app B).hom
  obtain ⟨r,hr,⟨J⟩⟩ := exists_orderCylinderHorn_realization_strongDeformation P V h
  let F := (SSet.toTop.map ψ).hom.comp r
  let a := sSetTopAdj.homEquiv D B (TopCat.ofHom (Y := B) (ε.comp F))
  have hε : ε.comp (SSet.toTop.map a).hom = ε.comp F := by
    have hh := (sSetTopAdj.homEquiv D B).symm_apply_apply (TopCat.ofHom (Y := B) (ε.comp F))
    rw [Adjunction.homEquiv_counit] at hh
    exact congrArg TopCat.Hom.hom hh
  have ha : i ≫ a = ψ := by
    apply (sSetTopAdj.homEquiv _ B).symm.injective
    rw [Adjunction.homEquiv_counit,Adjunction.homEquiv_counit]
    apply ConcreteCategory.hom_ext
    intro z
    change ε (SSet.toTop.map (i ≫ a) z) = ε (SSet.toTop.map ψ z)
    rw [Functor.map_comp,TopCat.comp_app]
    have hz := ContinuousMap.congr_fun hε (SSet.toTop.map i z)
    change ε (SSet.toTop.map a (SSet.toTop.map i z)) =
      ε (SSet.toTop.map ψ (r (SSet.toTop.map i z))) at hz
    exact hz.trans (congrArg (fun x => ε (SSet.toTop.map ψ x)) (hr z))
  let H₀ := J.compContinuousMap (SSet.toTop.map a).hom
  have h₀ : (SSet.toTop.map a).hom.comp ((SSet.toTop.map i).hom.comp r) = F := by
    apply ContinuousMap.ext
    intro z
    change SSet.toTop.map a (SSet.toTop.map i (r z)) = SSet.toTop.map ψ (r z)
    rw [← TopCat.comp_app,← Functor.map_comp,ha]
  have h₁ : (SSet.toTop.map a).hom.comp (ContinuousMap.id _) = (SSet.toTop.map a).hom := rfl
  refine ⟨r,a,ha,hε,H₀.cast h₀ h₁,J.toContinuousMap,?_⟩
  intro z
  rfl

end KIP126.StableHomotopy.Implementation
