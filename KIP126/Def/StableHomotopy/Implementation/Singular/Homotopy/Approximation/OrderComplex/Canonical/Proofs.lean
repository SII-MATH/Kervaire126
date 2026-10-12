module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.OrderComplex.Proofs
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.Subdivision.Iteration.LastVertex.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- A continuous map between finite order-complex realizations, followed
by an actual simplicial singular map, is homotopic to the realized
adjoint of its evaluation. Both the finite source and the actual finite
order factor in the target are proved inputs to the approximation step. -/
theorem singularEvaluation_orderComplex_canonical_homotopic
    (P Q : Type u) [PartialOrder P] [PartialOrder Q] [Fintype P] [Fintype Q]
    (B : TopCat.{u}) (ψ : nerve Q ⟶ TopCat.toSSet.obj B)
    (f : C(|nerve P|,|nerve Q|)) :
    ((SSet.toTop.map ψ).hom.comp f).Homotopic
      (SSet.toTop.map (sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B)
        ((sSetTopAdj.counit.app B).hom.comp ((SSet.toTop.map ψ).hom.comp f))))).hom := by
  let F := (SSet.toTop.map ψ).hom.comp f
  let ε := (sSetTopAdj.counit.app B).hom
  let a := sSetTopAdj.homEquiv (nerve P) B (TopCat.ofHom (Y := B) (ε.comp F))
  have hε : ε.comp (SSet.toTop.map a).hom = ε.comp F := by
    have h := (sSetTopAdj.homEquiv (nerve P) B).symm_apply_apply
      (TopCat.ofHom (Y := B) (ε.comp F))
    rw [Adjunction.homEquiv_counit] at h
    exact congrArg TopCat.Hom.hom h
  obtain ⟨n,φ,H,_,_⟩ := exists_iteratedOrderSubdivision_simplicial_approximation P Q f
  let e := iteratedOrderSubdivisionHomeomorph P (n+1)
  let ec : C(|nerve (iteratedOrderSubdivision P (n+1))|,|nerve P|) := ⟨e,e.continuous⟩
  let ei : C(|nerve P|,|nerve (iteratedOrderSubdivision P (n+1))|) := ⟨e.symm,e.symm.continuous⟩
  let ℓ := iteratedOrderSubdivisionLastVertex P (n+1)
  have hℓ : ec.Homotopic (SSet.toTop.map ℓ).hom :=
    iteratedOrderSubdivisionHomeomorph_homotopic_lastVertex P (n+1)
  have h₀ : (F.comp ec).Homotopic (SSet.toTop.map (φ ≫ ψ)).hom := by
    convert (ContinuousMap.Homotopic.refl (SSet.toTop.map ψ).hom).comp ⟨H⟩ using 1
    · rfl
    · ext x
      rw [Functor.map_comp,TopCat.comp_app]
      rfl
  have hh : (ε.comp (SSet.toTop.map (φ ≫ ψ)).hom).Homotopic
      (ε.comp (SSet.toTop.map (ℓ ≫ a)).hom) := by
    have h := ((ContinuousMap.Homotopic.refl ε).comp h₀).symm.trans
      ((ContinuousMap.Homotopic.refl (ε.comp F)).comp hℓ)
    convert h using 1
    ext x
    change ε (SSet.toTop.map (ℓ ≫ a) x) = ε (F (SSet.toTop.map ℓ x))
    rw [Functor.map_comp,TopCat.comp_app]
    exact ContinuousMap.congr_fun hε _
  have h₁ := (singularEvaluation_realized_homotopic_iff B (φ ≫ ψ) (ℓ ≫ a)).mp hh
  have h₂ : (SSet.toTop.map (ℓ ≫ a)).hom.Homotopic
      ((SSet.toTop.map a).hom.comp ec) := by
    convert (ContinuousMap.Homotopic.refl (SSet.toTop.map a).hom).comp hℓ.symm using 1
    ext x
    rw [Functor.map_comp,TopCat.comp_app]
    rfl
  have h := ((h₀.trans h₁).trans h₂).comp (ContinuousMap.Homotopic.refl ei)
  convert h using 1
  · ext x
    exact congrArg F (e.apply_symm_apply x).symm
  · ext x
    exact congrArg (SSet.toTop.map a) (e.apply_symm_apply x).symm

end KIP126.StableHomotopy.Implementation
