module

public import KIP126.Def.Topology.FiberBundle.OpenEmbedding.Data
public import KIP126.Def.Topology.FiberBundle.Chart.Proofs

@[expose] public section

namespace KIP126.Topology

variable {E A B F : Type*} [TopologicalSpace E] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace F]
set_option backward.isDefEq.respectTransparency false

/-- A local chart over an open embedded base neighborhood gives an
actual local chart of the original projection. -/
theorem localTriviality_at_of_openEmbedding [Nonempty F]
    (p : C(E,B)) (a : C(A,B)) (ha : _root_.Topology.IsOpenEmbedding a)
    (x : A) (T : Bundle.Trivialization F (pullbackSndMap p a)) (hx : x ∈ T.baseSet) :
    ∃ T' : Bundle.Trivialization F p, a x ∈ T'.baseSet := by
  let e := pullbackEmbeddingRestrictionHomeomorph p a ha.isEmbedding T.baseSet
  let b := ha.isEmbedding.homeomorphImage T.baseSet
  let h := e.symm.trans ((T.preimageHomeomorph (Set.Subset.refl T.baseSet)).trans
    (b.prodCongr (Homeomorph.refl F)))
  have hh (z : p ⁻¹' (a '' T.baseSet)) : (h z).1.val = p z.val := by
    change (b (T.preimageHomeomorph (Set.Subset.refl T.baseSet) (e.symm z)).1).val = _
    rw [Bundle.Trivialization.preimageHomeomorph_apply]
    exact (e.symm z).val.property.symm
  obtain ⟨T',_,hT'⟩ := FiberBundle.exists_trivialization_at_of_open_product p (a '' T.baseSet)
    (ha.isOpenMap _ T.open_baseSet) h hh (a x) ⟨x,hx,rfl⟩
  exact ⟨T',hT'⟩

end KIP126.Topology
