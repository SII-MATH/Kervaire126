module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Additive.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Zero.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The normalized ordinary source sphere map representing the coefficient
one. Its source is the specified sphere, identified with the point-set sphere
by `Prespectrum.sourceSphere_zero`. -/
noncomputable def SourceHF2Model.sourceUnit (M : SourceHF2Model) :
    Prespectrum.sourceSphere 0 ⟶ sourceLocalization.obj M.spectrum :=
  Prespectrum.sourceStableHomotopyEquiv M.spectrum 0 (M.pi0.symm 1)

/-- The normalized coefficient unit for the fully constructed fixed source. -/
noncomputable def sourceHF2Unit :
    Prespectrum.sourceSphere 0 ⟶ sourceLocalization.obj sourceHF2.spectrum :=
  sourceHF2.sourceUnit

end KIP126.StableHomotopy.Implementation
