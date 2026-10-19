module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import KIP126.Def.CategoryTheory.Preadditive.Scalar.Proofs

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ k : ℤ, (shiftFunctor C k).Additive] [Pretriangulated C]

set_option backward.isDefEq.respectTransparency false

/-- In the actual distinguished cofiber of multiplication by `n`, the
square of that scalar kills the identity. No exact order is asserted. -/
theorem nsmul_id_square_eq_zero_of_scalar_triangle
    {X Z : C} (n : ℕ) (g : X ⟶ Z) (δ : Z ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (n • 𝟙 X) g δ ∈ distTriang C) :
    (n*n) • 𝟙 Z = 0 := by
  let T := Triangle.mk (n • 𝟙 X) g δ
  have h₁ : g ≫ (n • 𝟙 Z) = 0 := by
    calc
      _ = (n • 𝟙 X) ≫ g := by simp
      _ = 0 := comp_distTriang_mor_zero₁₂ T hT
  obtain ⟨a,ha⟩ := T.yoneda_exact₃ hT (n • 𝟙 Z) h₁
  have h₂ : (n • 𝟙 Z) ≫ δ = 0 := by
    calc
      _ = δ ≫ (shiftFunctor C (1 : ℤ)).map (n • 𝟙 X) := by simp
      _ = 0 := comp_distTriang_mor_zero₃₁ T hT
  calc
    (n*n) • 𝟙 Z = (n • 𝟙 Z) ≫ (n • 𝟙 Z) := by simp [smul_smul]
    _ = (n • 𝟙 Z) ≫ (δ ≫ a) := congrArg (fun q => (n • 𝟙 Z) ≫ q) ha
    _ = 0 := by rw [← Category.assoc, h₂, zero_comp]

end KIP126.Foundation
