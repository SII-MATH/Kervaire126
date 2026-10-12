module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Square.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Strict simplicial replacement retains the entire actual canonical
singular lift of the prescribed boundary homotopy, not only its evaluated
image. This is the coherence needed to glue the realized homotopy itself. -/
theorem singularMap_replace_along_mono_with_lifted_homotopy
    {L K : SSet.{u}} (i : L ⟶ K) [Mono i]
    (B : TopCat.{u}) (f : K ⟶ TopCat.toSSet.obj B) (g : L ⟶ TopCat.toSSet.obj B)
    (H : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).Homotopy
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom)) :
    ∃ f' : K ⟶ TopCat.toSSet.obj B, i ≫ f' = g ∧
      ∃ G : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map f').hom,
        ∀ (t : I) (x : |L|), G (t,SSet.toTop.map i x) =
          singularCylinder L B (H.toContinuousMap.comp ContinuousMap.prodSwap) (x,t) := by
  obtain ⟨f',hf',H',hH'⟩ := singularMap_replace_along_mono_with_homotopy i B f g H
  let F : C(|K| × I,B) := H'.toContinuousMap.comp ContinuousMap.prodSwap
  let G : (SSet.toTop.map f).hom.Homotopy (SSet.toTop.map f').hom := {
    toFun := fun z => singularCylinder K B F (z.2,z.1)
    continuous_toFun := (singularCylinder K B F).continuous.comp
      (continuous_snd.prodMk continuous_fst)
    map_zero_left := singularCylinder_endpoint_of_realized B F f 0
      (fun x => H'.apply_zero x)
    map_one_left := singularCylinder_endpoint_of_realized B F f' 1
      (fun x => H'.apply_one x) }
  refine ⟨f',hf',G,?_⟩
  intro t x
  change singularCylinder K B F (SSet.toTop.map i x,t) = _
  rw [singularCylinder_precomp]
  apply congrArg (fun h : C(|L| × I,B) => singularCylinder L B h (x,t))
  apply ContinuousMap.ext
  intro z
  exact hH' z.2 z.1

end KIP126.StableHomotopy.Implementation
