module

public import KIP126.Def.StableHomotopy.InverseSequence.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasProductsOfShape ℕ C] [HasFunctorialCofiber (C := C)]

/-- A constructed sequential homotopy limit: the desuspended cofiber of
the actual difference map on the countable product. -/
noncomputable def InverseSequence.homotopyLimit (D : InverseSequence C) : C :=
  (HasFunctorialCofiber.cofib D.oneSubShift)⟦(-1 : ℤ)⟧

/-- The defining Milnor triangle of the constructed homotopy limit.
The inverse rotation fixes its signs and structure maps. -/
noncomputable def InverseSequence.homotopyLimitWitness (D : InverseSequence C) :
    SequentialHomotopyLimit D D.homotopyLimit where
  toProduct := (Triangle.mk D.oneSubShift (HasFunctorialCofiber.cofibι D.oneSubShift)
    (HasFunctorialCofiber.cofibδ D.oneSubShift)).invRotate.mor₁
  boundary := (Triangle.mk D.oneSubShift (HasFunctorialCofiber.cofibι D.oneSubShift)
    (HasFunctorialCofiber.cofibδ D.oneSubShift)).invRotate.mor₃
  distinguished := inv_rot_of_distTriang _ (HasFunctorialCofiber.cofib_distinguished D.oneSubShift)

end KIP126.StableHomotopy
