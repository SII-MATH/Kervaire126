module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.StableHomotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The actual stable-degree-zero equivalence obtained from the fixed
structure maps and specified normalized degree-zero coefficients. -/
noncomputable def coefficientStableZeroEquiv :
    Prespectrum.StableHomotopy hf2RealizationPrespectrum 0 ≃ ZMod 2 :=
  Equiv.ofBijective (coefficientStableCode hb) (coefficientStableCode_bijective hb)


end KIP126.StableHomotopy.Implementation.HF2Bond
