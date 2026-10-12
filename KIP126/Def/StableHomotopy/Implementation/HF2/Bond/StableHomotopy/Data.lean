module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Bond.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

variable (hb : ∀ n r, Function.Bijective (bondHomotopyMap n r))

/-- The coefficient map on the actual stable quotient, descended through
the proved homotopy and stabilization relations. -/
noncomputable def coefficientStableCode :
    Prespectrum.StableHomotopy hf2RealizationPrespectrum 0 → ZMod 2 :=
  Quot.lift (coefficientDiagonalRepresentative hb) fun _ _ h =>
    coefficientDiagonalRepresentative_relation hb h


end KIP126.StableHomotopy.Implementation.HF2Bond
