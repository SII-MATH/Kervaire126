module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Approximation.Extension.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Coproduct.Proofs
public import KIP126.Def.Topology.Coproduct.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory CategoryTheory.Limits Simplicial
open KIP126.Topology.SimplicialRealization
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Changing a singular map on one of two disjoint simplicial subobjects
can preserve its entire other restriction strictly, together with a homotopy
relative to that unchanged subobject. -/
theorem singularMap_replace_on_disjoint_subobjects {L M K : SSet.{u}}
    (i : L ⟶ K) (j : M ⟶ K) [Mono (simplicialSumDesc i j)] (B : TopCat.{u})
    (f : K ⟶ TopCat.toSSet.obj B) (g : L ⟶ TopCat.toSSet.obj B)
    (h : (((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
      (SSet.toTop.map i).hom).Homotopic
        ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom)) :
    ∃ f' : K ⟶ TopCat.toSSet.obj B,
      i ≫ f' = g ∧ j ≫ f' = j ≫ f ∧
      (SSet.toTop.map f).hom.HomotopicRel (SSet.toTop.map f').hom
        (Set.range (SSet.toTop.map j)) := by
  let c := simplicialSumDesc i j
  let g' := simplicialSumDesc g (j ≫ f)
  let F := ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
    (SSet.toTop.map c).hom
  let G := (sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g').hom
  let a := simplicialSumInl L M
  let b := simplicialSumInr L M
  have hFL : F.comp (SSet.toTop.map a).hom =
      ((sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map f).hom).comp
        (SSet.toTop.map i).hom := by
    change (((SSet.toTop.map a ≫ SSet.toTop.map c) ≫ SSet.toTop.map f) ≫
      sSetTopAdj.counit.app B).hom = _
    rw [← Functor.map_comp]
    rfl
  have hGL : G.comp (SSet.toTop.map a).hom =
      (sSetTopAdj.counit.app B).hom.comp (SSet.toTop.map g).hom := by
    change ((SSet.toTop.map a ≫ SSet.toTop.map g') ≫ sSetTopAdj.counit.app B).hom = _
    rw [← Functor.map_comp]
    rfl
  have hFGM : F.comp (SSet.toTop.map b).hom = G.comp (SSet.toTop.map b).hom := by
    change (((SSet.toTop.map b ≫ SSet.toTop.map c) ≫ SSet.toTop.map f) ≫
      sSetTopAdj.counit.app B).hom =
      ((SSet.toTop.map b ≫ SSet.toTop.map g') ≫ sSetTopAdj.counit.app B).hom
    simp only [← Functor.map_comp,b,c,g',← Category.assoc,simplicialSumInr_desc]
  obtain ⟨HL⟩ : (F.comp (SSet.toTop.map a).hom).Homotopic
      (G.comp (SSet.toTop.map a).hom) := by rwa [hFL,hGL]
  let HM : (F.comp (SSet.toTop.map b).hom).Homotopy
      (G.comp (SSet.toTop.map b).hom) := (ContinuousMap.Homotopy.refl _).cast rfl hFGM
  have hc := mapIsColimitOfPreservesOfIsColimit SSet.toTop a b (simplicialSum_isColimit L M)
  obtain ⟨H,_,hHM⟩ := KIP126.Topology.exists_homotopy_of_topological_coproduct hc F G HL HM
  obtain ⟨f',hf',H',hH'⟩ := singularMap_replace_along_mono_with_homotopy c B f g' H
  have hi : i ≫ f' = g := by
    have hh := congrArg (fun k => a ≫ k) hf'
    simpa only [a,c,g',← Category.assoc,simplicialSumInl_desc] using hh
  have hj : j ≫ f' = j ≫ f := by
    have hh := congrArg (fun k => b ≫ k) hf'
    simpa only [b,c,g',← Category.assoc,simplicialSumInr_desc] using hh
  refine ⟨f',hi,hj,?_⟩
  apply (singularEvaluation_realized_homotopicRel_iff B j f f').mp
  refine ⟨⟨H',?_⟩⟩
  intro t x hx
  obtain ⟨y,rfl⟩ := hx
  have hjc : SSet.toTop.map c (SSet.toTop.map b y) = SSet.toTop.map j y := by
    change (SSet.toTop.map b ≫ SSet.toTop.map c) y = _
    rw [← Functor.map_comp]
    rfl
  change H' (t,SSet.toTop.map j y) = _
  rw [← hjc,hH',hHM]
  exact rfl

end KIP126.StableHomotopy.Implementation
