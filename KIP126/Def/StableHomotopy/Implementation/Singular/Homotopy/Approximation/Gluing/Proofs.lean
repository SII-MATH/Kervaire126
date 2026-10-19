module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits Simplicial
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- Maps into the actual singular set glue across a genuine simplicial
pushout even when their evaluated boundary maps initially agree only
up to continuous homotopy. A strict replacement changes the first
piece by a homotopy and leaves the second piece exactly prescribed. -/
theorem singularMap_glue_along_homotopy {L K M P : SSet.{u}}
    {i : L ⟶ K} {j : L ⟶ M} {a : K ⟶ P} {b : M ⟶ P}
    (hp : IsPushout i j a b) [Mono i] (B : TopCat.{u})
    (f : K ⟶ TopCat.toSSet.obj B) (g : M ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
        (SSet.toTop.map i).hom).Homotopic
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom).comp
        (SSet.toTop.map j).hom)) :
    ∃ k : P ⟶ TopCat.toSSet.obj B, b ≫ k = g ∧
      (SSet.toTop.map f).hom.Homotopic (SSet.toTop.map (a ≫ k)).hom := by
  have h' : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).Homotopic
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (j ≫ g)).hom) := by
    convert h using 1
    ext x
    simp only [Functor.map_comp,TopCat.hom_comp]
    rfl
  obtain ⟨f',hf',H⟩ := singularMap_replace_along_mono i B f (j ≫ g) h'
  refine ⟨hp.desc f' g hf',hp.inr_desc f' g hf',?_⟩
  rw [hp.inl_desc]
  exact H

/-- The homotopy used for strict gluing retains every prescribed
relative simplicial region in the first piece. -/
theorem singularMap_glue_along_homotopy_rel {R L K M P : SSet.{u}}
    {i : L ⟶ K} {j : L ⟶ M} {a : K ⟶ P} {b : M ⟶ P}
    (hp : IsPushout i j a b) [Mono i] (t : R ⟶ L) (B : TopCat.{u})
    (f : K ⟶ TopCat.toSSet.obj B) (g : M ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
        (SSet.toTop.map i).hom).HomotopicRel
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom).comp
        (SSet.toTop.map j).hom) (Set.range (SSet.toTop.map t))) :
    ∃ k : P ⟶ TopCat.toSSet.obj B, b ≫ k = g ∧
      (SSet.toTop.map f).hom.HomotopicRel (SSet.toTop.map (a ≫ k)).hom
        (Set.range (SSet.toTop.map (t ≫ i))) := by
  have h' : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).HomotopicRel
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (j ≫ g)).hom)
        (Set.range (SSet.toTop.map t)) := by
    convert h using 1
    ext x
    simp only [Functor.map_comp,TopCat.hom_comp]
    rfl
  obtain ⟨f',hf',H⟩ := singularMap_replace_along_mono_rel i t B f (j ≫ g) h'
  refine ⟨hp.desc f' g hf',hp.inr_desc f' g hf',?_⟩
  rw [hp.inl_desc]
  exact H

end KIP126.StableHomotopy.Implementation
