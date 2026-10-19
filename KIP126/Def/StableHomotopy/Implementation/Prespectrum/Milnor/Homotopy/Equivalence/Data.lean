module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Milnor.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- The genuine finite-group Milnor comparison, as an additive equivalence
with the compatible families of the original stable homotopy groups. -/
noncomputable def sourceHomotopyLimitAddEquivOfFinite
    (D : InverseSequence SourceCategory.{0}) (d : ℤ)
    [∀ k, Finite ((sourceStableHomotopyAddFunctor (d+1)).obj (D.obj k))] :
    (sourceStableHomotopyAddFunctor d).obj (sourceHomotopyLimit D) ≃+
      sourceHomotopyCompatible D d :=
  AddEquiv.ofBijective (sourceHomotopyLimitComparison D d)
    (sourceHomotopyLimitComparison_bijective_of_finite D d)

end KIP126.StableHomotopy.Implementation
