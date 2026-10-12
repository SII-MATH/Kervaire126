module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The degreewise disjoint union of two actual simplicial sets. -/
def simplicialSum (K L : SSet.{u}) : SSet.{u} where
  obj a := K.obj a ⊕ L.obj a
  map f := ↾(Sum.map (K.map f) (L.map f))
  map_id a := by
    ext x
    cases x <;> simp
  map_comp f g := by
    ext x
    cases x <;> simp

/-- The first actual coproduct inclusion. -/
def simplicialSumInl (K L : SSet.{u}) : K ⟶ simplicialSum K L where
  app _ := ↾Sum.inl
  naturality _ _ _ := rfl

/-- The second actual coproduct inclusion. -/
def simplicialSumInr (K L : SSet.{u}) : L ⟶ simplicialSum K L where
  app _ := ↾Sum.inr
  naturality _ _ _ := rfl

/-- A pair of simplicial maps defines its actual disjoint-union map. -/
def simplicialSumDesc {K L T : SSet.{u}} (f : K ⟶ T) (g : L ⟶ T) :
    simplicialSum K L ⟶ T where
  app a := ↾(Sum.elim (f.app a) (g.app a))
  naturality a b k := by
    ext x
    cases x with
    | inl x => exact ConcreteCategory.congr_hom (f.naturality k) x
    | inr x => exact ConcreteCategory.congr_hom (g.naturality k) x

/-- The actual degreewise disjoint union has the genuine simplicial
coproduct universal property. -/
def simplicialSum_isColimit (K L : SSet.{u}) :
    IsColimit (BinaryCofan.mk (simplicialSumInl K L) (simplicialSumInr K L)) := by
  refine BinaryCofan.IsColimit.mk _ (fun f g => simplicialSumDesc f g)
    (fun f g => rfl) (fun f g => rfl) ?_
  intro T f g m hm₁ hm₂
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro x
  cases x with
  | inl x => exact ConcreteCategory.congr_hom (NatTrans.congr_app hm₁ a) x
  | inr x => exact ConcreteCategory.congr_hom (NatTrans.congr_app hm₂ a) x

end KIP126.Topology.SimplicialRealization
