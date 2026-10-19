module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.CylinderHorn.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Singular.Cylinder.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite MonoidalCategory
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The nerve of the ordered cylinder is exactly the actual simplicial
cylinder, with its time coordinate in the standard one-simplex. -/
def orderCylinderIso (P : Type u) [PartialOrder P] :
    nerve (OrderCylinder P) ≅ nerve P ⊗ Δ[1] where
  hom := {
    app d := TypeCat.ofHom fun s =>
      ((⟨fun k => (s.obj k).1,fun _ _ h => (s.monotone h).1⟩ :
        Fin (d.unop.len+1) →o P).monotone.functor,
        SSet.stdSimplex.objEquiv.symm (SimplexCategory.Hom.mk
          ⟨fun k => (s.obj k).2,fun _ _ h => (s.monotone h).2⟩))
    naturality := by
      intro d e f
      apply ConcreteCategory.hom_ext
      intro s
      apply Prod.ext
      · exact CategoryTheory.Functor.ext (fun _ => rfl)
      · apply SSet.stdSimplex.objEquiv.injective
        rfl }
  inv := {
    app d := TypeCat.ofHom fun s =>
      (⟨fun k => (s.1.obj k,(SSet.stdSimplex.objEquiv s.2).toOrderHom k),
        fun _ _ h => ⟨s.1.monotone h,(SSet.stdSimplex.objEquiv s.2).toOrderHom.monotone h⟩⟩ :
          Fin (d.unop.len+1) →o OrderCylinder P).monotone.functor
    naturality := by
      intro d e f
      apply ConcreteCategory.hom_ext
      intro s
      exact CategoryTheory.Functor.ext (fun _ => rfl) }
  hom_inv_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    exact CategoryTheory.Functor.ext (fun _ => rfl)
  inv_hom_id := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · exact CategoryTheory.Functor.ext (fun _ => rfl)
    · apply SSet.stdSimplex.objEquiv.injective
      change SimplexCategory.Hom.mk
        (⟨fun k => (SSet.stdSimplex.objEquiv s.2).toOrderHom k,
          (SSet.stdSimplex.objEquiv s.2).toOrderHom.monotone⟩) =
            SSet.stdSimplex.objEquiv s.2
      apply SimplexCategory.Hom.ext' _ _
      ext k
      rfl

/-- The actual geometric cylinder homeomorphism for any ordered set. -/
noncomputable def orderCylinderHomeomorph (P : Type u) [PartialOrder P] :
    |nerve (OrderCylinder P)| ≃ₜ (|nerve P| × I) :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (orderCylinderIso P))).trans
    (KIP126.StableHomotopy.Implementation.realizationCylinderHomeomorph (nerve P))

/-- The actual induced inclusion of the bottom-side horn into the
whole cone cylinder. -/
def orderCylinderHornEmbedding (P : Type u) [PartialOrder P] :
    OrderCylinderHorn P ↪o OrderCylinder (WithTop P) where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

def orderCylinderHornInclusion (P : Type u) [PartialOrder P] :
    nerve (OrderCylinderHorn P) ⟶ nerve (OrderCylinder (WithTop P)) :=
  nerveMap (orderCylinderHornEmbedding P).monotone.functor

noncomputable def orderCylinderHornRealizationInclusion (P : Type u) [PartialOrder P] :
    C(|nerve (OrderCylinderHorn P)|,|nerve (WithTop P)| × I) :=
  (⟨orderCylinderHomeomorph (WithTop P),
    (orderCylinderHomeomorph (WithTop P)).continuous⟩ : C(_,_)).comp
      (SSet.toTop.map (orderCylinderHornInclusion P)).hom

end KIP126.Topology.SimplicialRealization
