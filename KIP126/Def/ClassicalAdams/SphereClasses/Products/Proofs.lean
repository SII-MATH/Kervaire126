module

public import KIP126.Def.ClassicalAdams.SphereClasses.Products.Data
public import KIP126.Def.ClassicalAdams.SphereClasses.Product.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Comparison.Proofs
public import KIP126.Def.ClassicalAdams.MilnorCohomology.Multiplication.Proofs

@[expose] public section


set_option maxHeartbeats 1000000

/-! The named Milnor products agree with the internal E₂ multiplication.
These statements use the specified cobar product; comparison with the geometric
Adams tower pairing remains a separate obligation. -/
namespace KIP126.Classical.Adams.Sphere.Internal
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C)) (M : MilnorCooperations H)

/-- A product of named generators is the general internal product. -/
theorem hiProduct_eq_product (i j : ℕ) :
    hiProduct H M i j = product H M (hi H M i) (hi H M j) := by
  rw [← MilnorCohomology.comparison_hi H M i,
    ← MilnorCohomology.comparison_hi H M j, product_comparison]
  rfl

/-- The named square is the product of the named class with itself.
Only the equality of the displayed degrees requires transport. -/
theorem hiSquare_eq_product (i : ℕ) :
    hiSquare H M i = reindex H rfl (KIP126.Steenrod.Milnor.hiSquare_internalDegree i)
      (product H M (hi H M i) (hi H M i)) := by
  rw [← MilnorCohomology.comparison_hi H M i, product_comparison,
    reindex_comparison, ← MilnorCohomology.hiSquare_eq_cup,
    MilnorCohomology.comparison_hiSquare]

/-- The list code `[0, 3, 3]` is the same class as the named `h₀ h₃²`.
This is the concrete bridge needed by the one-line certificate. -/
theorem hMonomial_zero_three_eq_h0HiSquare :
    hMonomial H M [0, 3, 3] = h0HiSquare H M 3 := by
  unfold hMonomial
  simp only [hProduct, hWordDegree, reindex]
  rw [← MilnorCohomology.comparison_hi H M 0]
  rw [← MilnorCohomology.comparison_hi H M 3]
  have hinner := product_comparison H M
    (MilnorCohomology.hi H M 3) (MilnorCohomology.hi H M 3)
  rw [hinner]
  have houter := product_comparison H M
    (MilnorCohomology.hi H M 0)
    (MilnorCohomology.cup H M (MilnorCohomology.hi H M 3)
      (MilnorCohomology.hi H M 3))
  rw [houter]
  have hsq := (MilnorCohomology.hiSquare_eq_cup H M 3).symm
  unfold MilnorCohomology.cohomologyReindex at hsq
  have hsq_raw :
      MilnorCohomology.cup H M (MilnorCohomology.hi H M 3)
          (MilnorCohomology.hi H M 3) = MilnorCohomology.hiSquare H M 3 := by
    simpa using hsq
  rw [hsq_raw]
  unfold h0HiSquare
  have hs : 1 + (1 + 1 : ℕ) = 3 := by decide
  have ht : 2 ^ 0 + (2 ^ 3 + 2 ^ 3 : ℕ) = 1 + 2 ^ (3 + 1) := by decide
  cases hs
  cases ht
  rfl

end
end KIP126.Classical.Adams.Sphere.Internal
