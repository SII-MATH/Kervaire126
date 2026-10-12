module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.OrderComplex.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Approximation.Based.Proofs
public import KIP126.Def.Topology.Homotopy.Precomposition.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial Opposite
open KIP126.Topology KIP126.Topology.SimplicialRealization
open scoped unitInterval Classical

universe u

set_option backward.isDefEq.respectTransparency false

/-- Exact singular comparison is relative to the specified actual
vertex of a finite order-complex domain. -/
theorem singularEvaluation_realized_orderVertex_homotopicRel_iff (P : Type u)
    [PartialOrder P] [Fintype P] (B : TopCat.{u}) (p : P)
    (f g : nerve P ⟶ TopCat.toSSet.obj B) :
    ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).HomotopicRel
      ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom) {orderVertex P p} ↔
    (SSet.toTop.map f).hom.HomotopicRel (SSet.toTop.map g).hom {orderVertex P p} := by
  let R := ULift.{u} (Fin 1)
  let j : nerve R ⟶ nerve P := nerveMap (OrderHom.const R p).monotone.functor
  have hr : Set.range (SSet.toTop.map j) = {orderVertex P p} := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact orderConstant_realization R P p y
    · rintro rfl
      exact ⟨orderVertex R (ULift.up 0),orderConstant_realization R P p _⟩
  simpa only [hr] using singularEvaluation_realized_homotopicRel_iff B j f g

/-- For a based continuous map through an actual finite order-complex
simplicial map into the singular set, evaluation reflects nullhomotopy
relative to the original specified base vertex. -/
theorem singularEvaluation_orderComplex_based_nullHomotopic_iff (P Q : Type u)
    [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (B : TopCat.{u}) (ψ : nerve Q ⟶ TopCat.toSSet.obj B)
    (f : C(|nerve P|,|nerve Q|)) (p : P) (q : Q)
    (hf : f (orderVertex P p) = orderVertex Q q) :
    ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp f)).HomotopicRel
      (ContinuousMap.const _ (sSetTopAdj.counit.app B
        (SSet.toTop.map ψ (orderVertex Q q)))) {orderVertex P p} ↔
    ((SSet.toTop.map ψ).hom.comp f).HomotopicRel
      (ContinuousMap.const _ (SSet.toTop.map ψ (orderVertex Q q))) {orderVertex P p} := by
  constructor
  · intro h
    obtain ⟨n,φ,_,H⟩ := exists_iteratedOrderSubdivision_simplicial_approximation_based P Q f p q hf
    letI := iteratedOrderSubdivisionFintype P (n+1)
    let r := iteratedOrderSubdivisionVertex P (n+1) p
    let e := iteratedOrderSubdivisionHomeomorph P (n+1)
    let ec : C(|nerve (iteratedOrderSubdivision P (n+1))|,|nerve P|) := ⟨e,e.continuous⟩
    let ei : C(|nerve P|,|nerve (iteratedOrderSubdivision P (n+1))|) := ⟨e.symm,e.symm.continuous⟩
    have her : e (orderVertex _ r) = orderVertex P p :=
      iteratedOrderSubdivisionHomeomorph_vertex P (n+1) p
    have hei : e.symm (orderVertex P p) = orderVertex _ r := by
      rw [← her,e.symm_apply_apply]
    let c : nerve (iteratedOrderSubdivision P (n+1)) ⟶ nerve Q :=
      nerveMap (OrderHom.const _ q).monotone.functor
    have hc (x : |nerve (iteratedOrderSubdivision P (n+1))|) :
        SSet.toTop.map (c ≫ ψ) x = SSet.toTop.map ψ (orderVertex Q q) := by
      rw [Functor.map_comp,TopCat.comp_app]
      exact congrArg (SSet.toTop.map ψ) (orderConstant_realization _ Q q x)
    have ha : (((SSet.toTop.map ψ).hom.comp f).comp ec).HomotopicRel
        (SSet.toTop.map (φ ≫ ψ)).hom {orderVertex _ r} := by
      convert H.comp_continuousMap (SSet.toTop.map ψ).hom using 1
      · rfl
      · ext x
        simp [Functor.map_comp]
    have he : ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (φ ≫ ψ)).hom).HomotopicRel
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (c ≫ ψ)).hom) {orderVertex _ r} := by
      have hp := ha.symm.comp_continuousMap (sSetTopAdj.counit.app B).hom
      have hn := homotopicRel_precomp h ec (T := {orderVertex _ r})
        (by rintro x rfl; exact her)
      apply hp.trans
      convert hn using 1
      · rfl
      · ext x
        exact congrArg (sSetTopAdj.counit.app B) (hc x)
    have hl := (singularEvaluation_realized_orderVertex_homotopicRel_iff _ B r
      (φ ≫ ψ) (c ≫ ψ)).mp he
    have hh := homotopicRel_precomp (ha.trans hl) ei (T := {orderVertex P p})
      (by rintro x rfl; exact hei)
    convert hh using 1
    · ext x
      exact congrArg (fun y => SSet.toTop.map ψ (f y)) (e.apply_symm_apply x).symm
    · ext x
      exact (hc (ei x)).symm
  · intro h
    convert h.comp_continuousMap (sSetTopAdj.counit.app B).hom using 1
    ext x
    rfl

end KIP126.StableHomotopy.Implementation
