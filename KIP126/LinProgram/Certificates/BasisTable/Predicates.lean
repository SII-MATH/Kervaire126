import KIP126.LinProgram.Model.BasisTable.Data

namespace KIP126.LinE2
open KIP126.Core.Algebra

/-- The specific CSV monomials, not arbitrary chosen vectors, form a basis.
This asserts correct degrees, linear independence and spanning simultaneously. -/
def BasisTableCorrect (s t : ℕ) : Prop :=
  ∃ b : Module.Basis (BasisIndex s t) F2 (E2At s t),
    ∀ i, (b i).val = basisValue (basisRowAt s t i)

end KIP126.LinE2
