module

public import KIP126.Def.Topology.SimplicialRealization.Coproduct.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Data
public import KIP126.Def.Topology.SimplicialRealization.OrderComplex.MappingCylinder.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Coproduct.Proofs

@[expose] public section

section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

/-- The two disjoint ends, as one actual simplicial subobject of the
order mapping cylinder. -/
def orderMappingCylinderEndsInclusion {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) : simplicialSum (nerve P) (nerve Q) ⟶ nerve (OrderMappingCylinder f) :=
  simplicialSumDesc (orderMappingCylinderSourceInclusion f)
    (orderMappingCylinderTargetInclusion f)

end KIP126.Topology.SimplicialRealization

end

section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory

universe u

set_option backward.isDefEq.respectTransparency false

variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

/-- The actual two-end inclusion is degreewise injective. -/
instance orderMappingCylinderEndsInclusion_mono (f : P →o Q) :
    Mono (orderMappingCylinderEndsInclusion f) := by
  apply simplicialSumDesc_mono
  · intro a
    exact (CategoryTheory.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp inferInstance a)
  · intro a
    exact (CategoryTheory.mono_iff_injective _).mp
      ((NatTrans.mono_iff_mono_app _).mp inferInstance a)
  · intro a x y h
    have hh := congrArg (fun s : (nerve (OrderMappingCylinder f)).obj a =>
      s.obj (0 : Fin (a.unop.len + 1))) h
    change Sum.inl (x.obj 0) = Sum.inr (y.obj 0) at hh
    cases hh

/-- The first end is exactly the original source inclusion. -/
theorem orderMappingCylinderEndsInclusion_inl (f : P →o Q) :
    simplicialSumInl (nerve P) (nerve Q) ≫ orderMappingCylinderEndsInclusion f =
      orderMappingCylinderSourceInclusion f := rfl

/-- The second end is exactly the original target inclusion. -/
theorem orderMappingCylinderEndsInclusion_inr (f : P →o Q) :
    simplicialSumInr (nerve P) (nerve Q) ≫ orderMappingCylinderEndsInclusion f =
      orderMappingCylinderTargetInclusion f := rfl

end KIP126.Topology.SimplicialRealization

end
