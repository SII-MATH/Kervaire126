module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.OrderComplex.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy extension and adjunction produce a strict simplicial
replacement while retaining the whole prescribed evaluated boundary
homotopy, including all of its parameter values. -/
theorem singularMap_replace_along_mono_with_homotopy {L K : SSet.{u}} (i : L ⟶ K) [Mono i]
    (B : TopCat.{u}) (f : K ⟶ TopCat.toSSet.obj B) (g : L ⟶ TopCat.toSSet.obj B)
    (H : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).Homotopy
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom)) :
    ∃ f' : K ⟶ TopCat.toSSet.obj B, i ≫ f' = g ∧
      ∃ H' : ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).Homotopy
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f').hom),
        ∀ (t : I) (x : |L|), H' (t,SSet.toTop.map i x) = H (t,x) := by
  let p : C(|L| × I,B) := H.toContinuousMap.comp ContinuousMap.prodSwap
  obtain ⟨E,hE0,hEi⟩ := realization_mono_hasHomotopyExtension i B
    ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom) p
    (fun x => H.apply_zero x)
  let e₁ : C(|K|,B) := E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))
  let f' := sSetTopAdj.homEquiv K B (TopCat.ofHom (Y := B) e₁)
  have he : (sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f').hom = e₁ := by
    have hh := (sSetTopAdj.homEquiv K B).symm_apply_apply (TopCat.ofHom (Y := B) e₁)
    rw [Adjunction.homEquiv_counit] at hh
    exact congrArg TopCat.Hom.hom hh
  refine ⟨f',?_,?_⟩
  · apply (sSetTopAdj.homEquiv L B).symm.injective
    rw [Adjunction.homEquiv_counit,Adjunction.homEquiv_counit,Functor.map_comp]
    apply ConcreteCategory.hom_ext
    intro x
    change (sSetTopAdj.counit.app B).hom (SSet.toTop.map f' (SSet.toTop.map i x)) = _
    have hh := ContinuousMap.congr_fun he (SSet.toTop.map i x)
    change (sSetTopAdj.counit.app B).hom (SSet.toTop.map f' (SSet.toTop.map i x)) =
      E (SSet.toTop.map i x,1) at hh
    exact hh.trans ((hEi x 1).trans (H.apply_one x))
  · refine ⟨{
      toFun := fun z => E (z.2,z.1)
      continuous_toFun := E.continuous.comp (continuous_snd.prodMk continuous_fst)
      map_zero_left := hE0
      map_one_left := ?_ },fun t x => hEi x t⟩
    intro x
    exact (ContinuousMap.congr_fun he x).symm

/-- A continuous homotopy of the evaluated restriction along a genuine
simplicial subobject gives an exactly compatible simplicial replacement
homotopic to the original realized map. -/
theorem singularMap_replace_along_mono {L K : SSet.{u}} (i : L ⟶ K) [Mono i]
    (B : TopCat.{u}) (f : K ⟶ TopCat.toSSet.obj B) (g : L ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).Homotopic
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom)) :
    ∃ f' : K ⟶ TopCat.toSSet.obj B, i ≫ f' = g ∧
      (SSet.toTop.map f).hom.Homotopic (SSet.toTop.map f').hom := by
  obtain ⟨H⟩ := h
  obtain ⟨f',hf',H',_⟩ := singularMap_replace_along_mono_with_homotopy i B f g H
  exact ⟨f',hf',(singularEvaluation_realized_homotopic_iff B f f').mp ⟨H'⟩⟩

/-- Strict simplicial replacement also retains any relative region
that comes from a realized simplicial map into the prescribed boundary. -/
theorem singularMap_replace_along_mono_rel {M L K : SSet.{u}}
    (i : L ⟶ K) [Mono i] (j : M ⟶ L) (B : TopCat.{u})
    (f : K ⟶ TopCat.toSSet.obj B) (g : L ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).HomotopicRel
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom)
        (Set.range (SSet.toTop.map j))) :
    ∃ f' : K ⟶ TopCat.toSSet.obj B, i ≫ f' = g ∧
      (SSet.toTop.map f).hom.HomotopicRel (SSet.toTop.map f').hom
        (Set.range (SSet.toTop.map (j ≫ i))) := by
  obtain ⟨H⟩ := h
  obtain ⟨f',hf',H',hH'⟩ := singularMap_replace_along_mono_with_homotopy i B f g H.toHomotopy
  refine ⟨f',hf',?_⟩
  apply (singularEvaluation_realized_homotopicRel_iff B (j ≫ i) f f').mp
  refine ⟨⟨H',?_⟩⟩
  intro t x hx
  obtain ⟨y,rfl⟩ := hx
  rw [Functor.map_comp,TopCat.comp_app]
  exact (hH' t (SSet.toTop.map j y)).trans (H.eq_fst t (Set.mem_range_self y))

end KIP126.StableHomotopy.Implementation
