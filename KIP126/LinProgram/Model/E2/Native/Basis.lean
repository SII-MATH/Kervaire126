module

public import KIP126.LinProgram.Model.E2.Native.Data
public import KIP126.LinProgram.Model.BasisCatalogue.Data

@[expose] public section


/-! Native catalogue coordinates retain their original monomial interpretation.
These definitions make no assertion that the catalogue is a mathematical basis. -/
namespace KIP126.LinE2
noncomputable section

/-- Interpret the same archived monomial in the untruncated algebra. -/
def nativeBasisValue (row : BasisRow) : NativeAlgebra :=
  nativeProjection (monomialOfString row.monomial)

/-- The compatibility quotient preserves each native catalogue monomial. -/
@[simp] theorem truncate_basisValue (row : BasisRow) :
    truncate (nativeBasisValue row) = basisValue row := rfl

/-- In particular, the same degree-local CSV index denotes compatible values. -/
@[simp] theorem truncate_basisRowAt (s t : ℕ) (i : BasisIndex s t) :
    truncate (nativeBasisValue (basisRowAt s t i)) = basisValue (basisRowAt s t i) := rfl

end
end KIP126.LinE2
