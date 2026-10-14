module

public import Mathlib.CategoryTheory.Preadditive.Basic

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory

universe v u

/-- Maps from an object on which a scalar is invertible to an object
annihilated by that scalar vanish. This concerns actual morphisms. -/
theorem hom_subsingleton_of_nsmul_id_isIso
    {C : Type u} [Category.{v} C] [Preadditive C]
    (A B : C) (n : ℕ) [IsIso (n • 𝟙 A)] (hB : n • 𝟙 B = 0) :
    Subsingleton (A ⟶ B) := by
  have hz (f : A ⟶ B) : f = 0 := by
    apply (cancel_epi (n • 𝟙 A)).mp
    calc
      (n • 𝟙 A) ≫ f = f ≫ (n • 𝟙 B) := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp, Category.comp_id]
      _ = (n • 𝟙 A) ≫ 0 := by rw [hB]; simp
  exact ⟨fun f g => (hz f).trans (hz g).symm⟩

end KIP126.Foundation
