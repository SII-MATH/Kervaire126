import KIP126.Def.ClassicalAdams.Tmf.Multiplication.Data
import KIP126.Def.ClassicalAdams.Moss.Composition.CoefficientCycles.Layer.Proofs

namespace KIP126.Classical.Adams.Tmf

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [BraidedCategory C]
  (H : Mod2EilenbergMacLane (C := C)) (T : Mon C) (R : Mod2RingStructure H)
  [∀ A : C, (tensorRight A).CommShift ℤ]
  [∀ A : C, (tensorRight A).IsTriangulated]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]
  [(mod2UnitNatTrans H).CommShift ℤ] [MonoidalPreadditive C]

/-- The prescribed first-group product preserves second cycles. This is the
algebra-object analogue of the actual Moss layer kernel calculation, not an
assumed multiplication on a quotient page. Its proof is deferred. -/
theorem firstMultiplication_mem_secondCycles (s t s' t' : ℕ)
    (a : adamsCycles H.unit T.X 2 (by decide) s t)
    (b : adamsCycles H.unit T.X 2 (by decide) s' t') :
    firstMultiplication H T R s t s' t' a.val b.val ∈
      adamsCycles H.unit T.X 2 (by decide)
        ((s + s' : ℕ) : ℤ) ((t + t' : ℕ) : ℤ) := by
  sorry

end KIP126.Classical.Adams.Tmf
