module

public import KIP126.Def.StableHomotopy.Completion.Moore.ProductTriangle.Data

@[expose] public section

namespace KIP126.StableHomotopy

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]

theorem moorePowerTriangle_distinguished (p : ℕ) (X : C) (k : ℕ) :
    moorePowerTriangle p X k ∈ distTriang C :=
  HasFunctorialCofiber.cofib_distinguished _

variable [HasProductsOfShape ℕ C]

/-- Countable products retain the distinguished Moore stage triangle. -/
theorem mooreProductTriangle_distinguished (p : ℕ) (X : C) :
    mooreProductTriangle p X ∈ distTriang C :=
  productTriangle_distinguished _ (moorePowerTriangle_distinguished p X)

/-- Its first difference-map component is the scalar residual tower map. -/
theorem mooreProductTriangleDifference_hom₁ (p : ℕ) (X : C) :
    (mooreProductTriangleDifference p X).hom₁ =
      (scalarResidualSequence p X).oneSubShift := rfl

/-- Its second component is the constant identity tower map. -/
theorem mooreProductTriangleDifference_hom₂ (p : ℕ) (X : C) :
    (mooreProductTriangleDifference p X).hom₂ =
      (InverseSequence.constant X).oneSubShift := rfl

/-- Its third component is the specified Moore tower map. -/
theorem mooreProductTriangleDifference_hom₃ (p : ℕ) (X : C) :
    (mooreProductTriangleDifference p X).hom₃ =
      (moorePowerSequence p X).oneSubShift := rfl

end KIP126.StableHomotopy
