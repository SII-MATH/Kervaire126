import KIP126.Main.Solution.Computation.LinProgram.Basis.Data
import KIP126.LinProgram.Certificates.BasisTable.Predicates
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! The original basis properties, now consequences of the delivered actual
E₂ coordinates and their CSV compatibility in the one Challenge2 witness. -/

namespace KIP126.LinE2

open KIP126.Core.Algebra

theorem dataBasis_val (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    (dataBasis s t ht i).val = basisValue (basisRowAt s t i) :=
  KIP126.Main.StageInput.computation.results.sphereBasis.csv_values s t ht i

/-- Compatibility certification derived from the actual E₂ basis delivery.
The independent fixed-CSV certification remains an Interface helper. -/
theorem basisTable_correct (s t : ℕ) (ht : t ≤ 261) : BasisTableCorrect s t :=
  ⟨dataBasis s t ht, dataBasis_val s t ht⟩

theorem dataBasis_ne_zero (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    dataBasis s t ht i ≠ 0 := (dataBasis s t ht).ne_zero i

theorem dataCoordinates_basis (s t : ℕ) (ht : t ≤ 261) (i : BasisIndex s t) :
    dataCoordinates s t ht (dataBasis s t ht i) = Finsupp.single i 1 :=
  (dataBasis s t ht).repr_self i

/-- Reconstruct any element from its unique delivered coordinates. -/
theorem dataCoordinates_reconstruct (s t : ℕ) (ht : t ≤ 261) (x : E2At s t) :
    (dataCoordinates s t ht).symm (dataCoordinates s t ht x) = x :=
  (dataCoordinates s t ht).symm_apply_apply x

theorem data_finrank (s t : ℕ) (ht : t ≤ 261) :
    Module.finrank F2 (E2At s t) = (basisRowsAt s t).size := by
  simpa [BasisIndex] using Module.finrank_eq_card_basis (dataBasis s t ht)

end KIP126.LinE2
