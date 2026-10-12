module

public import KIP126.Def.Topology.SimplicialRealization.Product.Weak.Bijective.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Simplicial Opposite
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every continuous map from a compact space to a product of realizations
has a continuous lift to the realization of the simplicial product. -/
theorem continuousMap_lift_productComparison (X Y : SSet.{u})
    {D : Type*} [TopologicalSpace D] [CompactSpace D]
    (f : C(D,|X| × |Y|)) :
    ∃ g : C(D,|X ⊗ Y|), ∀ d, productComparison X Y (g d) = f d := by
  obtain ⟨A,hA,h,hf⟩ := continuousMap_factor_finite_simplicial_subcomplex Y
    (ContinuousMap.snd.comp f)
  letI := hA
  let e := realizationFiniteProductHomeomorph X A.toSSet
  let g := (SSet.toTop.map (𝟙 X ⊗ₘ A.ι)).hom.comp
    ((⟨e.symm,e.symm.continuous⟩ : C(_, _)).comp ((ContinuousMap.fst.comp f).prodMk h))
  refine ⟨g,?_⟩
  intro d
  have hn := ConcreteCategory.congr_hom
    (CartesianMonoidalCategory.prodComparison_natural SSet.toTop (𝟙 X) A.ι)
    (e.symm ((f d).1,h d))
  change productComparison X Y (g d) =
    (SSet.toTop.map (𝟙 X) (e (e.symm ((f d).1,h d))).1,
      SSet.toTop.map A.ι (e (e.symm ((f d).1,h d))).2) at hn
  simpa only [e.apply_symm_apply, CategoryTheory.Functor.map_id,
    TopCat.id_app, hf d, ContinuousMap.comp_apply, ContinuousMap.snd_apply, Prod.mk.eta] using hn

end KIP126.Topology.SimplicialRealization
