module

public import KIP126.Def.StableHomotopy.InverseSequence.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasProductsOfShape ℕ C]

/-- Countable products and actual distinguished cocones suffice to construct
a sequential homotopy limit; no tensor structure or cofiber choice is needed. -/
theorem InverseSequence.exists_homotopyLimit (D : InverseSequence C) :
    ∃ L : C, Nonempty (SequentialHomotopyLimit D L) := by
  obtain ⟨Z,g,h,hT⟩ := distinguished_cocone_triangle D.oneSubShift
  let T := Triangle.mk D.oneSubShift g h
  exact ⟨T.invRotate.obj₁,
    ⟨{ toProduct := T.invRotate.mor₁
       boundary := T.invRotate.mor₃
       distinguished := inv_rot_of_distTriang T hT }⟩⟩

end KIP126.StableHomotopy
