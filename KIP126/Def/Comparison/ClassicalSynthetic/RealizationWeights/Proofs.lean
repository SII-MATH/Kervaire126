import KIP126.Def.Comparison.ClassicalSynthetic.RealizationWeights.Data

/-! Weight comparisons for the SAME lambda-inversion realization.
Their zero value and every successive weight map are fixed, so this is
not a family of unrelated isomorphisms of objects of the same dimension.
The coefficient comparison is the already specified nu-recovery map.
-/
namespace KIP126.Comparison.ClassicalSynthetic
open CategoryTheory CategoryTheory.Functor
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context
open KIP126.Synthetic.SpectralSequence
universe u v w
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  (N : NuFunctorData C Syn) (L : LambdaRecovery N)

/-- Lambda inversion and the zero normalization determine every weight.
This uniqueness is a model comparison property, independent of Adams
labels, of the Lin output, and of any high-stem theorem. -/
theorem RealizationWeightComparison.unique
    (A B : RealizationWeightComparison N L) : A = B := by
  have he (X : C) (a : ℤ) : A.iso X a = B.iso X a := by
    have hi (a : ℤ) : IsIso (L.realization.map (weightLambdaArrow N X a)) := by
      have h : L.realization.map (weightLambdaArrow N X a) =
          (A.iso X (a-1)).hom ≫ (A.iso X a).inv := by
        rw [← A.lambda X a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rw [h]
      infer_instance
    induction a using Int.induction_on with
    | zero => exact Iso.ext ((A.zero X).trans (B.zero X).symm)
    | succ n ih =>
      apply Iso.ext
      letI := hi (n+1)
      apply (cancel_epi (L.realization.map (weightLambdaArrow N X (n+1)))).mp
      rw [A.lambda, B.lambda]
      have hn : (n : ℤ) + 1 - 1 = n := by omega
      rw [hn]
      exact congrArg Iso.hom ih
    | pred n ih =>
      apply Iso.ext
      rw [← A.lambda, ← B.lambda, ih]
  cases A with
  | mk a az al an =>
    cases B with
    | mk b bz bl bn =>
      have h : a = b := funext fun X => funext fun n => he X n
      cases h
      rfl

/-- Existence follows from inversion of the actual lambda maps and the
specified recovery at weight zero. It requires coherent index transports. -/
theorem realizationWeightComparison_exists (coherent : BiShiftCoherence Syn) :
    Nonempty (RealizationWeightComparison N L) := by sorry

end
end KIP126.Comparison.ClassicalSynthetic
