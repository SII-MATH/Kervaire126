module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Additive.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

/-- The specified coefficient equivalence, now as an equivalence of the
genuine stable abelian groups. -/
noncomputable def SourceHF2Model.pi0AddEquiv (M : SourceHF2Model) :
    Prespectrum.StableHomotopy M.spectrum 0 ≃+ ZMod 2 where
  toEquiv := M.pi0
  map_add' := M.pi0_map_add

/-- Additive recognition for the fully constructed fixed coefficient source. -/
noncomputable def sourceHF2PiZeroAddEquiv :
    Prespectrum.StableHomotopy sourceHF2.spectrum 0 ≃+ ZMod 2 :=
  sourceHF2.pi0AddEquiv

end KIP126.StableHomotopy.Implementation
