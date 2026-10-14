module

public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopy-compatible maps glue across an actual continuous attachment
along a realized simplicial subobject. The old-space map is retained
strictly, and the changed piece retains every parameter value of the
specified boundary homotopy. -/
theorem exists_map_of_realized_mono_attachment_with_homotopy
    {L K : SSet.{u}} (i : L ⟶ K) [Mono i] {A T Y : TopCat.{u}}
    (a : SSet.toTop.obj L ⟶ A) (u : A ⟶ T) (v : SSet.toTop.obj K ⟶ T)
    (hp : IsPushout a (SSet.toTop.map i) u v) (b : A ⟶ Y) (d : SSet.toTop.obj K ⟶ Y)
    (H : (d.hom.comp (SSet.toTop.map i).hom).Homotopy (b.hom.comp a.hom)) :
    ∃ r : T ⟶ Y, u ≫ r = b ∧
      ∃ H' : d.hom.Homotopy (v ≫ r).hom,
        ∀ (t : I) (x : |L|), H' (t,SSet.toTop.map i x) = H (t,x) := by
  let p : C(|L| × I,Y) := H.toContinuousMap.comp ContinuousMap.prodSwap
  obtain ⟨E,hE₀,hEi⟩ := realization_mono_hasHomotopyExtension i Y d.hom p
    (fun x => H.apply_zero x)
  let e₁ : SSet.toTop.obj K ⟶ Y :=
    TopCat.ofHom (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1)))
  have he : a ≫ b = SSet.toTop.map i ≫ e₁ := by
    ext x
    exact ((hEi x 1).trans (H.apply_one x)).symm
  let r := hp.desc b e₁ he
  have hv : v ≫ r = e₁ := hp.inr_desc _ _ _
  refine ⟨r,hp.inl_desc _ _ _,?_,?_⟩
  · exact {
      toFun := fun z => E (z.2,z.1)
      continuous_toFun := E.continuous.comp (continuous_snd.prodMk continuous_fst)
      map_zero_left := hE₀
      map_one_left := fun x => (ConcreteCategory.congr_hom hv x).symm }
  · intro t x
    exact hEi x t

end KIP126.Topology.SimplicialRealization
