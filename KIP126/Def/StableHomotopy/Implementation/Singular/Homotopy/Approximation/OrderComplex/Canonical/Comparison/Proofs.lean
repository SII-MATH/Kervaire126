module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.OrderComplex.Canonical.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.OrderComplex.Canonical.Based.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- Evaluation reflects homotopy between continuous maps with two
possibly different actual finite-order factors. Neither continuous
map between order complexes is required to be simplicial. -/
theorem singularEvaluation_orderComplex_homotopic_iff
    (P Q R : Type u) [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    [Fintype P] [Fintype Q] [Fintype R] (B : TopCat.{u})
    (ψ : nerve Q ⟶ TopCat.toSSet.obj B) (χ : nerve R ⟶ TopCat.toSSet.obj B)
    (f : C(|nerve P|,|nerve Q|)) (g : C(|nerve P|,|nerve R|)) :
    ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp f)).Homotopic
      ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map χ).hom.comp g)) ↔
    ((SSet.toTop.map ψ).hom.comp f).Homotopic ((SSet.toTop.map χ).hom.comp g) := by
  let F := (SSet.toTop.map ψ).hom.comp f
  let G := (SSet.toTop.map χ).hom.comp g
  let ε := (sSetTopAdj.counit.app B).hom
  let a := sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B) (ε.comp F))
  let b := sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B) (ε.comp G))
  have ha : ε.comp (SSet.toTop.map a).hom = ε.comp F := by
    exact congrArg TopCat.Hom.hom
      ((sSetTopAdj.homEquiv (nerve P) B).symm_apply_apply (TopCat.ofHom (Y := B) (ε.comp F)))
  have hb : ε.comp (SSet.toTop.map b).hom = ε.comp G := by
    exact congrArg TopCat.Hom.hom
      ((sSetTopAdj.homEquiv (nerve P) B).symm_apply_apply (TopCat.ofHom (Y := B) (ε.comp G)))
  constructor
  · intro h
    have hc : (ε.comp (SSet.toTop.map a).hom).Homotopic
        (ε.comp (SSet.toTop.map b).hom) := by rw [ha,hb]; exact h
    exact (singularEvaluation_orderComplex_canonical_homotopic P Q B ψ f).trans
      (((singularEvaluation_realized_homotopic_iff B a b).mp hc).trans
        (singularEvaluation_orderComplex_canonical_homotopic P R B χ g).symm)
  · intro h
    exact (ContinuousMap.Homotopic.refl ε).comp h

/-- The same two-factor comparison retains the specified actual base
vertex throughout the homotopy. -/
theorem singularEvaluation_orderComplex_homotopicRel_iff
    (P Q R : Type u) [PartialOrder P] [PartialOrder Q] [PartialOrder R]
    [Fintype P] [Fintype Q] [Fintype R] (B : TopCat.{u})
    (ψ : nerve Q ⟶ TopCat.toSSet.obj B) (χ : nerve R ⟶ TopCat.toSSet.obj B)
    (f : C(|nerve P|,|nerve Q|)) (g : C(|nerve P|,|nerve R|))
    (p : P) (q : Q) (r : R)
    (hf : f (orderVertex P p) = orderVertex Q q)
    (hg : g (orderVertex P p) = orderVertex R r) :
    ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp f)).HomotopicRel
      ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map χ).hom.comp g)) {orderVertex P p} ↔
    ((SSet.toTop.map ψ).hom.comp f).HomotopicRel ((SSet.toTop.map χ).hom.comp g)
      {orderVertex P p} := by
  let F := (SSet.toTop.map ψ).hom.comp f
  let G := (SSet.toTop.map χ).hom.comp g
  let ε := (sSetTopAdj.counit.app B).hom
  let a := sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B) (ε.comp F))
  let b := sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B) (ε.comp G))
  have ha : ε.comp (SSet.toTop.map a).hom = ε.comp F := by
    exact congrArg TopCat.Hom.hom
      ((sSetTopAdj.homEquiv (nerve P) B).symm_apply_apply (TopCat.ofHom (Y := B) (ε.comp F)))
  have hb : ε.comp (SSet.toTop.map b).hom = ε.comp G := by
    exact congrArg TopCat.Hom.hom
      ((sSetTopAdj.homEquiv (nerve P) B).symm_apply_apply (TopCat.ofHom (Y := B) (ε.comp G)))
  constructor
  · intro h
    have hc : (ε.comp (SSet.toTop.map a).hom).HomotopicRel
        (ε.comp (SSet.toTop.map b).hom) {orderVertex P p} := by rw [ha,hb]; exact h
    exact (singularEvaluation_orderComplex_canonical_homotopicRel P Q B ψ f p q hf).trans
      (((singularEvaluation_realized_orderVertex_homotopicRel_iff P B p a b).mp hc).trans
        (singularEvaluation_orderComplex_canonical_homotopicRel P R B χ g p r hg).symm)
  · intro h
    exact h.comp_continuousMap ε

end KIP126.StableHomotopy.Implementation
