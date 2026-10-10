import KIP126.Def.Steenrod.MilnorCoalgebra.Operations.Data

namespace KIP126.Steenrod.Milnor.Coalgebra

open CategoryTheory MonoidalCategory KIP126.Core.Algebra
  KIP126.Algebra.GradedVectorSpace

/-- Left counitality of the prescribed Milnor coproduct. -/
theorem comultiplication_counit_left :
    comultiplication ≫ counit ▷ dualSteenrodGraded =
      (λ_ dualSteenrodGraded).inv := by
  sorry

/-- Right counitality of the prescribed Milnor coproduct. -/
theorem comultiplication_counit_right :
    comultiplication ≫ dualSteenrodGraded ◁ counit =
      (ρ_ dualSteenrodGraded).inv := by
  sorry

/-- Coassociativity, with the actual Cauchy tensor associator. -/
theorem comultiplication_assoc :
    comultiplication ≫ dualSteenrodGraded ◁ comultiplication =
      comultiplication ≫ (comultiplication ▷ dualSteenrodGraded) ≫
        (α_ dualSteenrodGraded dualSteenrodGraded dualSteenrodGraded).hom := by
  sorry

/-- Extracting the constant coefficient of a constant returns that scalar. -/
theorem coaugmentationMap_counit :
    coaugmentationMap ≫ counit = 𝟙 (𝟙_ (GrVect F2)) := by
  sorry

/-- The actual constant polynomial is group-like. -/
theorem coaugmentationMap_comultiplication :
    coaugmentationMap ≫ comultiplication =
      (λ_ (𝟙_ (GrVect F2))).inv ≫
        (coaugmentationMap ⊗ₘ coaugmentationMap) := by
  sorry

end KIP126.Steenrod.Milnor.Coalgebra
