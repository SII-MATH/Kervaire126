module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial Opposite MonoidalCategory CartesianMonoidalCategory
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The adjunction's cylinder construction is exactly constant in time
on a map that already comes from an actual simplicial map. -/
theorem singularCylinder_static {K : SSet.{u}} (B : TopCat.{u})
    (f : K ⟶ TopCat.toSSet.obj B) (x : |K|) (t : I) :
    singularCylinder K B
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
        ContinuousMap.fst) (x,t) = SSet.toTop.map f x := by
  have h : singularCylinderAdjoint K B
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
        ContinuousMap.fst) = fst K Δ[1] ≫ f := by
    apply (sSetTopAdj.homEquiv _ _).symm.injective
    rw [singularCylinderAdjoint, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    apply ConcreteCategory.hom_ext
    intro z
    change sSetTopAdj.counit.app B
      (SSet.toTop.map f (SSet.toTop.map (fst K Δ[1]) z)) =
        sSetTopAdj.counit.app B (SSet.toTop.map (fst K Δ[1] ≫ f) z)
    rw [Functor.map_comp, TopCat.comp_app]
  change SSet.toTop.map (singularCylinderAdjoint K B _) _ = _
  rw [h, Functor.map_comp, TopCat.comp_app]
  have he := congrArg Prod.fst ((realizationCylinderHomeomorph K).apply_symm_apply (x,t))
  change SSet.toTop.map (fst K Δ[1]) ((realizationCylinderHomeomorph K).symm (x,t)) = x at he
  exact congrArg (SSet.toTop.map f) he

/-- A prescribed endpoint that is the evaluation of a realized simplicial
map lifts to that original realized map, not just to an unspecified lift. -/
theorem singularCylinder_endpoint_of_realized {K : SSet.{u}} (B : TopCat.{u})
    (H : C(|K| × I,B)) (f : K ⟶ TopCat.toSSet.obj B) (i : Fin 2)
    (hH : ∀ x, H (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      sSetTopAdj.counit.app B (SSet.toTop.map f x)) (x : |K|) :
    singularCylinder K B H (x,stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i)) =
      SSet.toTop.map f x := by
  rw [singularCylinder_endpoint]
  have h : TopCat.ofHom (Y := B)
      (H.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _
        (stdSimplexHomeomorphUnitInterval (stdSimplex.vertex i))))) =
        (sSetTopAdj.homEquiv K B).symm f := by
    rw [Adjunction.homEquiv_counit]
    exact ConcreteCategory.hom_ext _ _ hH
  rw [h, Equiv.apply_symm_apply]

/-- For maps that are realizations of simplicial maps into the actual
singular set, evaluation reflects continuous homotopies relative to any
realized simplicial subobject. The domain may have arbitrarily many cells. -/
theorem singularEvaluation_realized_homotopicRel_iff
    {K L : SSet.{u}} (B : TopCat.{u}) (j : L ⟶ K)
    (f g : K ⟶ TopCat.toSSet.obj B) :
    ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).HomotopicRel
      ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom)
      (Set.range (SSet.toTop.map j)) ↔
    (SSet.toTop.map f).hom.HomotopicRel (SSet.toTop.map g).hom
      (Set.range (SSet.toTop.map j)) := by
  constructor
  · rintro ⟨H⟩
    let h : C(|K| × I,B) := H.toContinuousMap.comp ContinuousMap.prodSwap
    refine ⟨{
      toFun := fun z => singularCylinder K B h (z.2,z.1)
      continuous_toFun := (singularCylinder K B h).continuous.comp
        (continuous_snd.prodMk continuous_fst)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro x
      exact singularCylinder_endpoint_of_realized B h f 0 (fun y => H.apply_zero y) x
    · intro x
      exact singularCylinder_endpoint_of_realized B h g 1 (fun y => H.apply_one y) x
    · intro t x hx
      obtain ⟨y,rfl⟩ := hx
      change singularCylinder K B h (SSet.toTop.map j y,t) =
        SSet.toTop.map f (SSet.toTop.map j y)
      rw [singularCylinder_precomp]
      have he : h.comp ((SSet.toTop.map j).hom.prodMap (ContinuousMap.id I)) =
          (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (j ≫ f)).hom).comp
            ContinuousMap.fst) := by
        apply ContinuousMap.ext
        intro z
        change H (z.2, SSet.toTop.map j z.1) =
          sSetTopAdj.counit.app B (SSet.toTop.map (j ≫ f) z.1)
        rw [Functor.map_comp, TopCat.comp_app]
        exact H.eq_fst z.2 (Set.mem_range_self z.1)
      rw [he, singularCylinder_static, Functor.map_comp, TopCat.comp_app]
  · intro h
    exact h.comp_continuousMap (sSetTopAdj.counit.app B).hom

end KIP126.StableHomotopy.Implementation
