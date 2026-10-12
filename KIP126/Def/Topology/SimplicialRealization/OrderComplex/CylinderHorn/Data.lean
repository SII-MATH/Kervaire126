module

public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCone.Data

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The ordered cylinder, retaining its order category rather than the
independently inferred product-category instance. -/
def OrderCylinder (P : Type u) := P × Fin 2

instance orderCylinder_partialOrder (P : Type u) [PartialOrder P] :
    PartialOrder (OrderCylinder P) := inferInstanceAs (PartialOrder (P × Fin 2))

instance orderCylinder_finite (P : Type u) [Finite P] :
    Finite (OrderCylinder P) := inferInstanceAs (Finite (P × Fin 2))

/-- The bottom and side of the cylinder on an actual order cone. The
missing vertex is precisely the upper copy of the cone apex. -/
def OrderCylinderHorn (P : Type u) [PartialOrder P] :=
  {z : WithTop P × Fin 2 // z.2 = 0 ∨ z.1 ≠ ⊤}

instance orderCylinderHorn_partialOrder (P : Type u) [PartialOrder P] :
    PartialOrder (OrderCylinderHorn P) := inferInstanceAs (PartialOrder (Subtype _))

instance orderCylinderHorn_finite (P : Type u) [PartialOrder P] [Finite P] :
    Finite (OrderCylinderHorn P) := inferInstanceAs (Finite (Subtype _))

/-- The entire bottom of the cone cylinder. -/
def orderCylinderHornBottomEmbedding (P : Type u) [PartialOrder P] :
    WithTop P ↪o OrderCylinderHorn P where
  toFun p := ⟨(p,0),Or.inl rfl⟩
  inj' := by intro p q h; exact congrArg (fun z => z.val.1) h
  map_rel_iff' := by intro p q; change (p ≤ q ∧ (0 : Fin 2) ≤ 0) ↔ p ≤ q; simp

/-- The entire side cylinder on the base of the cone. -/
def orderCylinderHornSideEmbedding (P : Type u) [PartialOrder P] :
    OrderCylinder P ↪o OrderCylinderHorn P where
  toFun p := ⟨((p.1 : WithTop P),p.2),Or.inr WithTop.coe_ne_top⟩
  inj' := by
    intro p q h
    apply Prod.ext
    · exact WithTop.coe_injective (congrArg (fun z => z.val.1) h)
    · exact congrArg (fun z => z.val.2) h
  map_rel_iff' := by
    intro p q
    change (((p.1 : WithTop P) ≤ (q.1 : WithTop P)) ∧ p.2 ≤ q.2) ↔ _
    rw [WithTop.coe_le_coe]
    rfl

/-- The lower endpoint inclusion into the side cylinder. -/
def orderCylinderHornCornerEmbedding (P : Type u) [PartialOrder P] :
    P ↪o OrderCylinder P where
  toFun p := (p,0)
  inj' := by intro p q h; exact congrArg Prod.fst h
  map_rel_iff' := by intro p q; change (p ≤ q ∧ (0 : Fin 2) ≤ 0) ↔ p ≤ q; simp

def orderCylinderHornBottomInclusion (P : Type u) [PartialOrder P] :
    nerve (WithTop P) ⟶ nerve (OrderCylinderHorn P) :=
  nerveMap (orderCylinderHornBottomEmbedding P).monotone.functor

def orderCylinderHornSideInclusion (P : Type u) [PartialOrder P] :
    nerve (OrderCylinder P) ⟶ nerve (OrderCylinderHorn P) :=
  nerveMap (orderCylinderHornSideEmbedding P).monotone.functor

def orderCylinderHornCornerInclusion (P : Type u) [PartialOrder P] :
    nerve P ⟶ nerve (OrderCylinder P) :=
  nerveMap (orderCylinderHornCornerEmbedding P).monotone.functor

end KIP126.Topology.SimplicialRealization
