module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Comparison.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Approximation.Homotopy.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Constant.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial Opposite
open KIP126.Topology.SimplicialRealization
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Evaluation reflects ordinary homotopies between actual realized
simplicial maps, by the same exact singular-cylinder endpoint laws. -/
theorem singularEvaluation_realized_homotopic_iff {K : SSet.{u}} (B : TopCat.{u})
    (f g : K ⟶ TopCat.toSSet.obj B) :
    ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).Homotopic
      ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom) ↔
    (SSet.toTop.map f).hom.Homotopic (SSet.toTop.map g).hom := by
  constructor
  · rintro ⟨H⟩
    let h : C(|K| × I,B) := H.toContinuousMap.comp ContinuousMap.prodSwap
    refine ⟨{
      toFun := fun z => singularCylinder K B h (z.2,z.1)
      continuous_toFun := (singularCylinder K B h).continuous.comp
        (continuous_snd.prodMk continuous_fst)
      map_zero_left := fun x =>
        singularCylinder_endpoint_of_realized B h f 0 (fun y => H.apply_zero y) x
      map_one_left := fun x =>
        singularCylinder_endpoint_of_realized B h g 1 (fun y => H.apply_one y) x }⟩
  · intro h
    exact (ContinuousMap.Homotopic.refl (sSetTopAdj.counit.app B).hom).comp h

/-- For maps factoring through an actual finite order complex by an
actual simplicial map to the singular set, evaluation detects ordinary
nullhomotopy. The intermediate continuous map need not be simplicial. -/
theorem singularEvaluation_orderComplex_nullHomotopic_iff (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (B : TopCat.{u}) (ψ : nerve Q ⟶ TopCat.toSSet.obj B)
    (f : C(|nerve P|,|nerve Q|)) (q : Q) :
    ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp f)).Homotopic
      (ContinuousMap.const _ (sSetTopAdj.counit.app B
        (SSet.toTop.map ψ (orderVertex Q q)))) ↔
    ((SSet.toTop.map ψ).hom.comp f).Homotopic
      (ContinuousMap.const _ (SSet.toTop.map ψ (orderVertex Q q))) := by
  constructor
  · intro h
    obtain ⟨n,φ,H,_,_⟩ := exists_iteratedOrderSubdivision_simplicial_approximation P Q f
    letI := iteratedOrderSubdivisionFintype P (n+1)
    let e := iteratedOrderSubdivisionHomeomorph P (n+1)
    let ec : C(|nerve (iteratedOrderSubdivision P (n+1))|,|nerve P|) :=
      ⟨e,e.continuous⟩
    let ei : C(|nerve P|,|nerve (iteratedOrderSubdivision P (n+1))|) :=
      ⟨e.symm,e.symm.continuous⟩
    let c : nerve (iteratedOrderSubdivision P (n+1)) ⟶ nerve Q :=
      nerveMap (OrderHom.const _ q).monotone.functor
    have hc (x : |nerve (iteratedOrderSubdivision P (n+1))|) :
        SSet.toTop.map (c ≫ ψ) x = SSet.toTop.map ψ (orderVertex Q q) := by
      rw [Functor.map_comp,TopCat.comp_app]
      exact congrArg (SSet.toTop.map ψ) (orderConstant_realization _ Q q x)
    have ha : (((SSet.toTop.map ψ).hom.comp f).comp ec).Homotopic
        (SSet.toTop.map (φ ≫ ψ)).hom := by
      convert (ContinuousMap.Homotopic.refl (SSet.toTop.map ψ).hom).comp ⟨H⟩ using 1
      · rfl
      · ext x
        simp [Functor.map_comp]
    have he : ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (φ ≫ ψ)).hom).Homotopic
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (c ≫ ψ)).hom) := by
      have hp := (ContinuousMap.Homotopic.refl (sSetTopAdj.counit.app B).hom).comp ha.symm
      have hn := h.comp (ContinuousMap.Homotopic.refl ec)
      apply hp.trans
      convert hn using 1
      · rfl
      · ext x
        exact congrArg (sSetTopAdj.counit.app B) (hc x)
    have hl := (singularEvaluation_realized_homotopic_iff B (φ ≫ ψ) (c ≫ ψ)).mp he
    have hh := (ha.trans hl).comp (ContinuousMap.Homotopic.refl ei)
    convert hh using 1
    · ext x
      exact congrArg (fun y => SSet.toTop.map ψ (f y)) (e.apply_symm_apply x).symm
    · ext x
      exact (hc (ei x)).symm
  · intro h
    simpa only [ContinuousMap.comp_const] using
      (ContinuousMap.Homotopic.refl (sSetTopAdj.counit.app B).hom).comp h

end KIP126.StableHomotopy.Implementation
