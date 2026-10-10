import KIP126.Def.Algebra.GradedComodule.Tensor.Raw.Data

/-! Naturality and laws of the explicitly given right-tensor maps. These
generic statements are separated from the data; their proofs are not part
of the current statement-definition milestone. -/

namespace KIP126.Algebra.GradedComodule.RightTensor

open CategoryTheory MonoidalCategory

universe u v

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

theorem counit_naturality (C : Comon V) {X Y : V} (f : X ⟶ Y) :
    (tensorRight C.X).map f ≫ counitApp C Y = counitApp C X ≫ f := by
  sorry

theorem comul_naturality (C : Comon V) {X Y : V} (f : X ⟶ Y) :
    (tensorRight C.X).map f ≫ comulApp C Y =
      comulApp C X ≫ (tensorRight C.X).map ((tensorRight C.X).map f) := by
  sorry

theorem coassoc (C : Comon V) (X : V) :
    comulApp C X ≫ (tensorRight C.X).map (comulApp C X) =
      comulApp C X ≫ comulApp C (X ⊗ C.X) := by
  sorry

theorem left_counit (C : Comon V) (X : V) :
    comulApp C X ≫ counitApp C (X ⊗ C.X) = 𝟙 (X ⊗ C.X) := by
  sorry

theorem right_counit (C : Comon V) (X : V) :
    comulApp C X ≫ (tensorRight C.X).map (counitApp C X) = 𝟙 (X ⊗ C.X) := by
  sorry

theorem trivial_counit {C : Comon V} (η : Coaugmentation C) (X : V) :
    trivialCoaction η X ≫ counitApp C X = 𝟙 X := by
  sorry

theorem trivial_coassoc {C : Comon V} (η : Coaugmentation C) (X : V) :
    trivialCoaction η X ≫ comulApp C X =
      trivialCoaction η X ≫ (tensorRight C.X).map (trivialCoaction η X) := by
  sorry

theorem trivial_naturality {C : Comon V} (η : Coaugmentation C)
    {X Y : V} (f : X ⟶ Y) :
    trivialCoaction η X ≫ (tensorRight C.X).map f = f ≫ trivialCoaction η Y := by
  sorry

end KIP126.Algebra.GradedComodule.RightTensor
