module

public import KIP126.Def.Topology.FiberBundle.Pullback.Data
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace KIP126.Topology

variable {E A B : Type*} [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]
set_option backward.isDefEq.respectTransparency false

/-- Along an embedding, restriction of the actual pullback is exactly
restriction of the original total space to the image of the base set. -/
noncomputable def pullbackEmbeddingRestrictionHomeomorph (p : C(E,B)) (a : C(A,B))
    (ha : _root_.Topology.IsEmbedding a) (U : Set A) :
    (pullbackSndMap p a ⁻¹' U) ≃ₜ (p ⁻¹' (a '' U)) := by
  let e := ha.homeomorphImage U
  let b : C(p ⁻¹' (a '' U),U) :=
    ⟨fun x => e.symm ⟨p x.val,x.property⟩,
      e.symm.continuous.comp ((p.continuous.comp continuous_subtype_val).subtype_mk _)⟩
  have hb (x : p ⁻¹' (a '' U)) : a (b x).val = p x.val :=
    congrArg Subtype.val (e.apply_symm_apply ⟨p x.val,x.property⟩)
  exact {
    toFun := fun z => ⟨z.val.val.1,⟨z.val.val.2,z.property,z.val.property.symm⟩⟩
    invFun := fun x => ⟨⟨(x.val,(b x).val),(hb x).symm⟩,(b x).property⟩
    left_inv := fun z => by
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rfl
      · exact ha.injective ((hb _).trans z.val.property)
    right_inv := fun _ => rfl
    continuous_toFun :=
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.prodMk (continuous_subtype_val.comp b.continuous)).subtype_mk _ |>.subtype_mk _ }

end KIP126.Topology
