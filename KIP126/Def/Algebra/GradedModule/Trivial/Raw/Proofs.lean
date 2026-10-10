import KIP126.Def.Algebra.GradedModule.Trivial.Raw.Data

/-! Unit and associativity of restriction along the specified augmentation. -/

namespace KIP126.Algebra.GradedModule

open CategoryTheory MonoidalCategory
open scoped MonObj

universe u v
variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem trivialAction_unit {A : Mon V} (ε : Augmentation A) (X : V) :
    (η[A.X] ▷ X) ≫ trivialAction ε X = (λ_ X).hom := by
  set_option backward.isDefEq.respectTransparency false in
    simp [trivialAction, ← comp_whiskerRight_assoc, Mon.trivial]

theorem trivialAction_assoc {A : Mon V} (ε : Augmentation A) (X : V) :
    (μ[A.X] ▷ X) ≫ trivialAction ε X =
      (α_ A.X A.X X).hom ≫ (A.X ◁ trivialAction ε X) ≫ trivialAction ε X := by
  set_option backward.isDefEq.respectTransparency false in
    simp only [trivialAction, ← comp_whiskerRight_assoc, IsMonHom.mul_hom]
    simp only [comp_whiskerRight, Category.assoc, whiskerLeft_comp]
    change ((ε.hom ⊗ₘ ε.hom) ▷ X) ≫ ((λ_ (𝟙_ V)).hom ▷ X) ≫ (λ_ X).hom = _
    dsimp only [Mon.trivial]
    rw [whisker_exchange_assoc ε.hom (λ_ X).hom]
    rw [← tensorHom_def'_assoc]
    rw [← tensorHom_id ε.hom X, ← tensorHom_id (ε.hom ⊗ₘ ε.hom) X]
    rw [← associator_naturality_assoc]
    congr 1
    monoidal_coherence

end KIP126.Algebra.GradedModule
