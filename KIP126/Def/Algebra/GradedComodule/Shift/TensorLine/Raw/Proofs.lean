import KIP126.Def.Algebra.GradedComodule.Shift.TensorLine.Raw.Data

/-! Inverse and coaction identities for the prescribed degree-line maps. -/

namespace KIP126.Algebra.GradedComodule.TensorLine

open CategoryTheory MonoidalCategory GradedVectorSpace
open scoped TensorProduct

universe u

variable (K : Type u) [Field K]

/-- The prescribed splitting is inverse to multiplication on the tensor lines. -/
theorem hom_inv_id (t u : ℤ) :
    hom K t u ≫ inv K t u = 𝟙 (degreeLine K t ⊗ degreeLine K u) := by
  sorry

/-- Multiplying the prescribed splitting returns the original degree line. -/
theorem inv_hom_id (t u : ℤ) :
    inv K t u ≫ hom K t u = 𝟙 (degreeLine K (t + u)) := by
  sorry

/-- On the nonzero summand the forward map is the actual scalar product. -/
theorem hom_tensor (t u : ℤ) (a b : K) :
    (hom K t u (t + u)).hom
        ((tensorInclusion K (degreeLine K t) (degreeLine K u) t u (t + u) rfl).hom
          ((GradedObject.singleObjApplyIso t (ModuleCat.of K K)).inv.hom a ⊗ₜ[K]
            (GradedObject.singleObjApplyIso u (ModuleCat.of K K)).inv.hom b)) =
      (GradedObject.singleObjApplyIso (t + u) (ModuleCat.of K K)).inv.hom (a * b) := by
  sorry

/-- The inverse takes the chosen generator to the two chosen generators. -/
theorem inv_generator (t u : ℤ) :
    (inv K t u (t + u)).hom (degreeLineGenerator K (t + u)) =
      (tensorInclusion K (degreeLine K t) (degreeLine K u) t u (t + u) rfl).hom
        (degreeLineGenerator K t ⊗ₜ[K] degreeLineGenerator K u) := by
  sorry

/-- The prescribed multiplication intertwines the actual shifted trivial
coaction with the trivial coaction in the sum degree. -/
theorem hom_coaction {C : Comon (GrVect K)} (η : Coaugmentation C) (t u : ℤ) :
    ((internalShift K C t).obj (trivialAt K η u)).a ≫
        (rightTensorComonad C).map (hom K t u) =
      hom K t u ≫ (trivialAt K η (t + u)).a := by
  sorry

end KIP126.Algebra.GradedComodule.TensorLine
