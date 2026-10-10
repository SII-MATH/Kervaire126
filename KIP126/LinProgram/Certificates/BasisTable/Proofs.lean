import KIP126.LinProgram.Certificates.BasisTable.Data
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace KIP126.LinE2

open KIP126.Core.Algebra

theorem basisOfCertification_val (s t : ℕ) (h : BasisTableCorrect s t)
    (i : BasisIndex s t) :
    (basisOfCertification s t h i).val = basisValue (basisRowAt s t i) :=
  Classical.choose_spec h i

theorem basisOfCertification_ne_zero (s t : ℕ) (h : BasisTableCorrect s t)
    (i : BasisIndex s t) : basisOfCertification s t h i ≠ 0 :=
  (basisOfCertification s t h).ne_zero i

theorem coordinatesOfCertification_basis (s t : ℕ) (h : BasisTableCorrect s t)
    (i : BasisIndex s t) :
    coordinatesOfCertification s t h (basisOfCertification s t h i) =
      Finsupp.single i 1 :=
  (basisOfCertification s t h).repr_self i

/-- Reconstruct an arbitrary element from its unique certified coordinates. -/
theorem coordinatesOfCertification_reconstruct (s t : ℕ) (h : BasisTableCorrect s t)
    (x : E2At s t) :
    (coordinatesOfCertification s t h).symm (coordinatesOfCertification s t h x) = x :=
  (coordinatesOfCertification s t h).symm_apply_apply x

theorem finrank_ofCertification (s t : ℕ) (h : BasisTableCorrect s t) :
    Module.finrank F2 (E2At s t) = (basisRowsAt s t).size := by
  simpa [BasisIndex] using Module.finrank_eq_card_basis (basisOfCertification s t h)

end KIP126.LinE2
