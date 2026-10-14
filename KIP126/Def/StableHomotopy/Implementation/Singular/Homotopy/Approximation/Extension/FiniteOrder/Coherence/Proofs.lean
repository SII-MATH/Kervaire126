module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.FiniteOrder.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Geometry.Deformation.Proofs
public import KIP126.Def.Topology.Homotopy.Precomposition.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- An actual map on a disk cylinder whose bottom and side are already
one realized simplicial map is homotopic to the realized adjoint of its
evaluation, fixing that whole horn. The upper face is allowed to vary. -/
theorem singularEvaluation_orderCylinder_canonical_homotopicRel_horn
    (P V : Type u) [PartialOrder P] [Fintype V]
    (h : |nerve (WithTop P)| ≃ₜ stdSimplex ℝ V) (B : TopCat.{u})
    (F : C(|nerve (OrderCylinder (WithTop P))|,|TopCat.toSSet.obj B|))
    (ψ : nerve (OrderCylinderHorn P) ⟶ TopCat.toSSet.obj B)
    (hF : ∀ z, F (SSet.toTop.map (orderCylinderHornInclusion P) z) = SSet.toTop.map ψ z) :
    F.HomotopicRel
      (SSet.toTop.map (sSetTopAdj.homEquiv _ B (TopCat.ofHom (Y := B)
        ((sSetTopAdj.counit.app B).hom.comp F)))).hom
      (Set.range (SSet.toTop.map (orderCylinderHornInclusion P))) := by
  let D := nerve (OrderCylinder (WithTop P))
  let i := orderCylinderHornInclusion P
  let ε := (sSetTopAdj.counit.app B).hom
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
    exact hz.trans (congrArg ε (hF z))
  obtain ⟨R,hR,H⟩ := exists_orderCylinderHorn_strongDeformation P V h
  let e := orderCylinderHomeomorph (WithTop P)
  let ec : C(|D|,|nerve (WithTop P)| × I) := ⟨e,e.continuous⟩
  let ei : C(|nerve (WithTop P)| × I,|D|) := ⟨e.symm,e.symm.continuous⟩
  let r := R.comp ec
  have hpre := homotopicRel_precomp H ec
    (T := Set.range (SSet.toTop.map i)) (by
      rintro _ ⟨z,rfl⟩
      exact ⟨z,rfl⟩)
  have HD : (ContinuousMap.id |D|).HomotopicRel ((SSet.toTop.map i).hom.comp r)
      (Set.range (SSet.toTop.map i)) := by
    have hD := hpre.comp_continuousMap ei
    convert hD using 1
    · ext x
      exact (e.symm_apply_apply x).symm
    · ext x
      exact (e.symm_apply_apply (SSet.toTop.map i (r x))).symm
  have HF : F.HomotopicRel ((SSet.toTop.map ψ).hom.comp r)
      (Set.range (SSet.toTop.map i)) := by
    convert HD.comp_continuousMap F using 1
    · rfl
    · ext x
      exact (hF (r x)).symm
  have HA : (SSet.toTop.map a).hom.HomotopicRel ((SSet.toTop.map ψ).hom.comp r)
      (Set.range (SSet.toTop.map i)) := by
    convert HD.comp_continuousMap (SSet.toTop.map a).hom using 1
    · rfl
    · ext x
      change SSet.toTop.map ψ (r x) = SSet.toTop.map a (SSet.toTop.map i (r x))
      rw [← TopCat.comp_app,← Functor.map_comp,ha]
  exact HF.trans HA.symm

/-- Apply the relative horn comparison to the actual cone on any
finite subdivision of a standard simplex boundary, with no geometric
homeomorphism premise left to supply. The upper face remains free. -/
theorem singularEvaluation_iteratedOrderBoundaryCylinder_canonical_homotopicRel_horn
    (V : Type u) [LinearOrder V] [Fintype V] [Nontrivial V]
    [Fintype (orderProperChains V)] (n : ℕ) (B : TopCat.{u})
    (F : C(|nerve (OrderCylinder (WithTop
      (iteratedOrderSubdivision (orderProperChains V) n)))|,|TopCat.toSSet.obj B|))
    (ψ : nerve (OrderCylinderHorn (iteratedOrderSubdivision (orderProperChains V) n)) ⟶
      TopCat.toSSet.obj B)
    (hF : ∀ z, F (SSet.toTop.map (orderCylinderHornInclusion
      (iteratedOrderSubdivision (orderProperChains V) n)) z) = SSet.toTop.map ψ z) :
    F.HomotopicRel
      (SSet.toTop.map (sSetTopAdj.homEquiv _ B (TopCat.ofHom (Y := B)
        ((sSetTopAdj.counit.app B).hom.comp F)))).hom
      (Set.range (SSet.toTop.map (orderCylinderHornInclusion
        (iteratedOrderSubdivision (orderProperChains V) n)))) := by
  obtain ⟨h,_,_⟩ := exists_iteratedOrderBoundaryCone_stdSimplex_homeomorph V n
  exact singularEvaluation_orderCylinder_canonical_homotopicRel_horn _ V h B F ψ hF

end KIP126.StableHomotopy.Implementation
