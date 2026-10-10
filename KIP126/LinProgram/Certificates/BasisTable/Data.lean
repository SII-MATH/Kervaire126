import KIP126.LinProgram.Certificates.BasisTable.Predicates

/-!
Basis and coordinates obtained from an explicit certification of the fixed CSV
values. This construction does not assume that certification has been proved
and imports no stage witness or fixed certification theorem.
-/

namespace KIP126.LinE2

open KIP126.Core.Algebra

/-- Choose the basis certified to have precisely the displayed CSV values. -/
noncomputable def basisOfCertification (s t : ℕ) (h : BasisTableCorrect s t) :
    Module.Basis (BasisIndex s t) F2 (E2At s t) :=
  Classical.choose h

/-- The coordinates of the same certified basis. -/
noncomputable def coordinatesOfCertification (s t : ℕ) (h : BasisTableCorrect s t) :
    E2At s t ≃ₗ[F2] (BasisIndex s t →₀ F2) :=
  (basisOfCertification s t h).repr

/-- Reference a certified basis value by its CSV index, with safe failure. -/
noncomputable def basisByCSVOfCertification? (s t : ℕ) (h : BasisTableCorrect s t)
    (index : ℕ) : Option (E2At s t) :=
  (findBasisIndex? s t index).map (basisOfCertification s t h)

end KIP126.LinE2
