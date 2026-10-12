module

public import KIP126.Def.Topology.SimplicialRealization.Horn.Proofs
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial

universe u

set_option backward.isDefEq.respectTransparency false

/-- A compatible singular horn fills by precomposing its continuous
adjoint with the explicit retraction of the topological simplex onto
its specified horn. No local regularity assumption on the space is used. -/
theorem singular_horn_filler (B : TopCat.{u}) (n : ℕ) (i : Fin (n+2))
    (f : (Λ[n+1,i] : SSet.{u}) ⟶ TopCat.toSSet.obj B) :
    ∃ g : (Δ[n+1] : SSet.{u}) ⟶ TopCat.toSSet.obj B,
      (Λ[n+1,i]).ι ≫ g = f := by
  obtain ⟨r,hr⟩ := KIP126.Topology.SimplicialRealization.exists_horn_realization_retraction.{u} n i
  let h := (sSetTopAdj.homEquiv _ B).symm f
  let g := sSetTopAdj.homEquiv _ B (TopCat.ofHom r ≫ h)
  refine ⟨g,?_⟩
  apply (sSetTopAdj.homEquiv _ B).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm]
  change SSet.toTop.map (Λ[n+1,i]).ι ≫
    (sSetTopAdj.homEquiv _ B).symm (sSetTopAdj.homEquiv _ B (TopCat.ofHom r ≫ h)) = h
  rw [Equiv.symm_apply_apply]
  apply ConcreteCategory.hom_ext
  intro x
  change h (r (SSet.toTop.map (Λ[n+1,i]).ι x)) = h x
  exact congrArg h (hr x)

/-- The actual singular simplicial set of every topological space is a
Kan complex, with fillers supplied by the geometric horn retractions. -/
theorem singular_kanComplex (B : TopCat.{u}) :
    SSet.KanComplex (TopCat.toSSet.obj B) := by
  apply SSet.KanComplex.iff.mpr
  intro n i f hf
  obtain ⟨g,hg⟩ := singular_horn_filler B n i hf.desc
  refine ⟨g,?_⟩
  intro j hj
  rw [← SSet.horn.ι_ι i j hj,Category.assoc,hg]
  exact hf.ι_desc j hj

/-- Continuous maps out of a realized simplicial set extend across every
actual simplicial anodyne extension. This transfers the established Kan
lifting property through the realization--singular adjunction. -/
theorem continuousMap_extend_realization_anodyne
    {K L : SSet.{u}} (i : K ⟶ L) (hi : SSet.anodyneExtensions i)
    (B : TopCat.{u}) (f : C(|K|,B)) :
    ∃ g : C(|L|,B), ∀ x, g (SSet.toTop.map i x) = f x := by
  open CategoryTheory.Limits HomotopicalAlgebra SSet.modelCategoryQuillen in
  letI := singular_kanComplex B
  haveI : HasLiftingProperty i (CategoryTheory.Limits.terminal.from (TopCat.toSSet.obj B)) := by
    apply hi
    rw [← HomotopicalAlgebra.fibration_iff]
    infer_instance
  let f' := sSetTopAdj.homEquiv K B (TopCat.ofHom f)
  have sq : CommSq f' i (CategoryTheory.Limits.terminal.from (TopCat.toSSet.obj B))
      (CategoryTheory.Limits.terminal.from L) := ⟨by simp⟩
  refine ⟨((sSetTopAdj.homEquiv L B).symm sq.lift).hom,?_⟩
  have h : i ≫ sq.lift = f' := sq.fac_left
  have he := congrArg (sSetTopAdj.homEquiv K B).symm h
  rw [Adjunction.homEquiv_naturality_left_symm] at he
  change SSet.toTop.map i ≫ (sSetTopAdj.homEquiv L B).symm sq.lift =
    (sSetTopAdj.homEquiv K B).symm (sSetTopAdj.homEquiv K B (TopCat.ofHom f)) at he
  rw [Equiv.symm_apply_apply] at he
  intro x
  exact ConcreteCategory.congr_hom he x

/-- The realization of every anodyne extension admits an actual continuous
retraction; this is obtained by extending the identity map, not by an
assumed topological comparison. -/
theorem exists_realization_anodyne_retraction
    {K L : SSet.{u}} (i : K ⟶ L) (hi : SSet.anodyneExtensions i) :
    ∃ r : C(|L|,|K|), ∀ x, r (SSet.toTop.map i x) = x :=
  continuousMap_extend_realization_anodyne i hi (SSet.toTop.obj K) (ContinuousMap.id _)

end KIP126.StableHomotopy.Implementation
