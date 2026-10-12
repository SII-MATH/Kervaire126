module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Contractible.Iso.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Pretriangulated
universe u

/-- Every contractible triangle in the original localization is
isomorphic to an actual standard fiber triangle. -/
theorem source_contractibleTriangle_iso_exists (A : SourceCategory.{u}) :
    ∃ (X Y : Prespectrum.{u}) (f : X ⟶ Y),
      Nonempty (contractibleTriangle A ≅ sourceFiberTriangle f) := by
  rcases A with ⟨⟨A⟩⟩
  exact ⟨A,zeroPrespectrum,zeroMap A zeroPrespectrum,⟨(sourceFiberZeroTriangleIso A).symm⟩⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
