import KIP126.Def.Steenrod.MilnorCoalgebra.Antipode.Data

/-! Exact compatibility of the constructed graded map with its polynomial
formula and the existing coalgebra operations. No Hopf structure or module
duality is asserted by these property statements. -/

namespace KIP126.Steenrod.Milnor.Coalgebra.Antipode

open CategoryTheory MonoidalCategory KIP126.Core.Algebra

theorem polynomial_map (n : ℤ) (x : Carrier n) :
    polynomial n ((map n).hom x) = polynomialMap (polynomial n x) := by
  sorry

theorem map_involutive : map ≫ map = 𝟙 dualSteenrod.X := by
  sorry

theorem map_counit : map ≫ counit = counit := by
  sorry

theorem coaugmentation_map : coaugmentationMap ≫ map = coaugmentationMap := by
  sorry

/-- Anti-comultiplicativity states the necessary braiding explicitly; it
does not replace the original comultiplication by a swapped convention. -/
theorem map_comultiplication :
    map ≫ comultiplication =
      comultiplication ≫ (map ⊗ₘ map) ≫ (β_ dualSteenrod.X dualSteenrod.X).hom := by
  sorry

end KIP126.Steenrod.Milnor.Coalgebra.Antipode
