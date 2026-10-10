import KIP126.Def.StableHomotopy.DescendingTower.Data

/-! The actual cofiber layers and triangle maps of the specified adjacent
tower arrows. No comparison with a different chosen cofiber is implicit. -/

namespace KIP126.StableHomotopy.DescendingTower

open CategoryTheory CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C)

/-- The chosen cofiber of the actual adjacent arrow at filtration `k`. -/
def layer (k : ℤ) : C := HasFunctorialCofiber.cofib (T.step k)

/-- The specified map from the tower term into its layer. -/
def layerIncl (k : ℤ) : T.obj k ⟶ T.layer k :=
  HasFunctorialCofiber.cofibι (T.step k)

/-- The specified connecting arrow into the suspension of the next term. -/
def layerBoundary (k : ℤ) : T.layer k ⟶ (T.obj (k + 1))⟦(1 : ℤ)⟧ :=
  HasFunctorialCofiber.cofibδ (T.step k)

/-- The actual cofiber triangle of the adjacent tower arrow. -/
def layerTriangle (k : ℤ) : Triangle C :=
  Triangle.mk (T.step k) (T.layerIncl k) (T.layerBoundary k)

/-- The same specified layer triangle, bundled for represented-Hom
connecting maps. Its objects and all three arrows are unchanged. -/
def layerCofiberSequence (k : ℤ) : HoCofiberSequence (C := C) where
  X := T.obj (k + 1)
  Y := T.obj k
  Z := T.layer k
  f := T.step k
  g := T.layerIncl k
  h := T.layerBoundary k
  distinguished := HasFunctorialCofiber.cofib_distinguished (T.step k)

end KIP126.StableHomotopy.DescendingTower
