module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.Disjoint.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits Simplicial
open KIP126.Topology.SimplicialRealization

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy-compatible singular maps glue across an actual pushout
while strictly preserving a disjoint subobject of the changed piece. -/
theorem singularMap_glue_along_homotopy_fixing_disjoint {L K M P R : SSet.{u}}
    {i : L ⟶ K} {j : L ⟶ M} {a : K ⟶ P} {b : M ⟶ P}
    (hp : IsPushout i j a b) (t : R ⟶ K) [Mono (simplicialSumDesc i t)]
    (B : TopCat.{u}) (f : K ⟶ TopCat.toSSet.obj B) (g : M ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
        (SSet.toTop.map i).hom).Homotopic
      (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom).comp
        (SSet.toTop.map j).hom)) :
    ∃ k : P ⟶ TopCat.toSSet.obj B,
      b ≫ k = g ∧ t ≫ a ≫ k = t ≫ f ∧
      (SSet.toTop.map f).hom.HomotopicRel (SSet.toTop.map (a ≫ k)).hom
        (Set.range (SSet.toTop.map t)) := by
  have h' : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).Homotopic
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map (j ≫ g)).hom) := by
    convert h using 1
    ext x
    simp only [Functor.map_comp,TopCat.hom_comp]
    rfl
  obtain ⟨f',hf',ht,H⟩ := singularMap_replace_on_disjoint_subobjects i t B f (j ≫ g) h'
  refine ⟨hp.desc f' g hf',hp.inr_desc f' g hf',?_,?_⟩
  · rw [hp.inl_desc]
    exact ht
  · rw [hp.inl_desc]
    exact H

end KIP126.StableHomotopy.Implementation
