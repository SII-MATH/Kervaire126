module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.OrderComplex.Based.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.LastVertex.Based.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- The canonicalization of a map with an actual finite-order factor
retains its specified base vertex throughout the homotopy. -/
theorem singularEvaluation_orderComplex_canonical_homotopicRel
    (P Q : Type u) [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (B : TopCat.{u}) (ψ : nerve Q ⟶ TopCat.toSSet.obj B)
    (f : C(|nerve P|,|nerve Q|)) (p : P) (q : Q)
    (hf : f (orderVertex P p) = orderVertex Q q) :
    ((SSet.toTop.map ψ).hom.comp f).HomotopicRel
      (SSet.toTop.map (sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B)
        ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp f))))).hom
      {orderVertex P p} := by
  let F := (SSet.toTop.map ψ).hom.comp f
  let ε := (sSetTopAdj.counit.app B).hom
  let a := sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B) (ε.comp F))
  have hε : ε.comp (SSet.toTop.map a).hom = ε.comp F := by
    have h := (sSetTopAdj.homEquiv (nerve P) B).symm_apply_apply
      (TopCat.ofHom (Y := B) (ε.comp F))
    rw [Adjunction.homEquiv_counit] at h
    exact congrArg TopCat.Hom.hom h
  obtain ⟨n,φ,_,H⟩ := exists_iteratedOrderSubdivision_simplicial_approximation_based P Q f p q hf
  letI := iteratedOrderSubdivisionFintype P (n+1)
  let r := iteratedOrderSubdivisionVertex P (n+1) p
  let e := iteratedOrderSubdivisionHomeomorph P (n+1)
  let ec : C(|nerve (iteratedOrderSubdivision P (n+1))|,|nerve P|) := ⟨e,e.continuous⟩
  let ei : C(|nerve P|,|nerve (iteratedOrderSubdivision P (n+1))|) := ⟨e.symm,e.symm.continuous⟩
  let ℓ := iteratedOrderSubdivisionLastVertex P (n+1)
  have hℓ : ec.HomotopicRel (SSet.toTop.map ℓ).hom {orderVertex _ r} :=
    iteratedOrderSubdivisionHomeomorph_homotopicRel_lastVertex P (n+1) p
  have h₀ : (F.comp ec).HomotopicRel (SSet.toTop.map (φ ≫ ψ)).hom {orderVertex _ r} := by
    convert H.comp_continuousMap (SSet.toTop.map ψ).hom using 1
    · rfl
    · ext x
      rw [Functor.map_comp,TopCat.comp_app]
      rfl
  have hh : (ε.comp (SSet.toTop.map (φ ≫ ψ)).hom).HomotopicRel
      (ε.comp (SSet.toTop.map (ℓ ≫ a)).hom) {orderVertex _ r} := by
    have h := (h₀.comp_continuousMap ε).symm.trans (hℓ.comp_continuousMap (ε.comp F))
    convert h using 1
    ext x
    change ε (SSet.toTop.map (ℓ ≫ a) x) = ε (F (SSet.toTop.map ℓ x))
    rw [Functor.map_comp,TopCat.comp_app]
    exact ContinuousMap.congr_fun hε _
  have h₁ := (singularEvaluation_realized_orderVertex_homotopicRel_iff _ B r
    (φ ≫ ψ) (ℓ ≫ a)).mp hh
  have h₂ : (SSet.toTop.map (ℓ ≫ a)).hom.HomotopicRel
      ((SSet.toTop.map a).hom.comp ec) {orderVertex _ r} := by
    convert hℓ.symm.comp_continuousMap (SSet.toTop.map a).hom using 1
    ext x
    rw [Functor.map_comp,TopCat.comp_app]
    rfl
  have hei : e.symm (orderVertex P p) = orderVertex _ r := by
    apply e.injective
    rw [Homeomorph.apply_symm_apply]
    exact (iteratedOrderSubdivisionHomeomorph_vertex P (n+1) p).symm
  have h := homotopicRel_precomp ((h₀.trans h₁).trans h₂) ei
    (T := {orderVertex P p}) (by rintro x rfl; exact hei)
  convert h using 1
  · ext x
    exact congrArg F (e.apply_symm_apply x).symm
  · ext x
    exact congrArg (SSet.toTop.map a) (e.apply_symm_apply x).symm

end KIP126.StableHomotopy.Implementation
